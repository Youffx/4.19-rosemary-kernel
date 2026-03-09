/*
 * Implementation of the security services.
 *
 * Authors : Stephen Smalley, <sds@tycho.nsa.gov>
 *	     James Morris <jmorris@redhat.com>
 *
 * Updated: Trusted Computer Solutions, Inc. <dgoeddel@trustedcs.com>
 *
 *	Support for enhanced MLS infrastructure.
 *	Support for context based audit filters.
 *
 * Updated: Frank Mayer <mayerf@tresys.com> and Karl MacMillan <kmacmillan@tresys.com>
 *
 *	Added conditional policy language extensions
 *
 * Updated: Hewlett-Packard <paul@paul-moore.com>
 *
 * Added support for NetLabel
 * Added support for the policy capability bitmap
 *
 * Updated: Chad Sellers <csellers@tresys.com>
 *
 * Added validation of kernel classes and permissions
 *
 * Updated: KaiGai Kohei <kaigai@ak.jp.nec.com>
 *
 * Added support for bounds domain and audit messaged on masked permissions
 *
 * Updated: Guido Trentalancia <guido@trentalancia.com>
 *
 * Added support for runtime switching of the policy type
 *
 * Copyright (C) 2008, 2009 NEC Corporation
 * Copyright (C) 2006, 2007 Hewlett-Packard Development Company, L.P.
 * Copyright (C) 2004-2006 Trusted Computer Solutions, Inc.
 * Copyright (C) 2003 - 2004, 2006 Tresys Technology, LLC
 * Copyright (C) 2003 Red Hat, Inc., James Morris <jmorris@redhat.com>
 *	This program is free software; you can redistribute it and/or modify
 *	it under the terms of the GNU General Public License as published by
 *	the Free Software Foundation, version 2.
 */
#include <linux/kernel.h>
#include <linux/slab.h>
#include <linux/string.h>
#include <linux/spinlock.h>
#include <linux/rcupdate.h>
#include <linux/errno.h>
#include <linux/in.h>
#include <linux/sched.h>
#include <linux/audit.h>
#include <linux/mutex.h>
#include <linux/selinux.h>
#include <linux/flex_array.h>
#include <linux/vmalloc.h>
#include <net/netlabel.h>

#include "flask.h"
#include "avc.h"
#include "avc_ss.h"
#include "security.h"
#include "context.h"
#include "policydb.h"
#include "sidtab.h"
#include "services.h"
#include "conditional.h"
#include "mls.h"
#include "objsec.h"
#include "netlabel.h"
#include "xfrm.h"
#include "ebitmap.h"
#include "audit.h"

const char *selinux_policycap_names[__POLICYDB_CAPABILITY_MAX] = {
	"network_peer_controls",
	"open_perms",
	"extended_socket_class",
	"always_check_network",
	"cgroup_seclabel",
	"nnp_nosuid_transition"
};

static struct selinux_ss selinux_ss;

void selinux_ss_init(struct selinux_ss **ss)
{
	rwlock_init(&selinux_ss.policy_rwlock);
	mutex_init(&selinux_ss.status_lock);
	*ss = &selinux_ss;
}

static int context_struct_to_string(struct policydb *policydb,
				    struct context *context,
				    char **scontext,
				    u32 *scontext_len);

static void context_struct_compute_av(struct policydb *policydb,
				      struct context *scontext,
				      struct context *tcontext,
				      u16 tclass,
				      struct av_decision *avd,
				      struct extended_perms *xperms);

static int selinux_set_mapping(struct policydb *pol,
			       struct security_class_mapping *map,
			       struct selinux_map *out_map)
{
	u16 i, j;
	unsigned k;
	bool print_unknown_handle = false;

	if (!map)
		return -EINVAL;
	i = 0;
	while (map[i].name)
		i++;

	out_map->mapping = kcalloc(++i, sizeof(*out_map->mapping), GFP_ATOMIC);
	if (!out_map->mapping)
		return -ENOMEM;

	j = 0;
	while (map[j].name) {
		struct security_class_mapping *p_in = map + (j++);
		struct selinux_mapping *p_out = out_map->mapping + j;

		if (!strcmp(p_in->name, "")) {
			p_out->num_perms = 0;
			continue;
		}

		p_out->value = string_to_security_class(pol, p_in->name);
		if (!p_out->value) {
			pr_info("SELinux:  Class %s not defined in policy.\n",
			       p_in->name);
			if (pol->reject_unknown)
				goto err;
			p_out->num_perms = 0;
			print_unknown_handle = true;
			continue;
		}

		k = 0;
		while (p_in->perms[k]) {
			if (!*p_in->perms[k]) {
				k++;
				continue;
			}
			p_out->perms[k] = string_to_av_perm(pol, p_out->value,
							    p_in->perms[k]);
			if (!p_out->perms[k]) {
				pr_info("SELinux:  Permission %s in class %s not defined in policy.\n",
				       p_in->perms[k], p_in->name);
				if (pol->reject_unknown)
					goto err;
				print_unknown_handle = true;
			}

			k++;
		}
		p_out->num_perms = k;
	}

	if (print_unknown_handle)
		pr_info("SELinux: the above unknown classes and permissions will be %s\n",
		       pol->allow_unknown ? "allowed" : "denied");

	out_map->size = i;
	return 0;
err:
	kfree(out_map->mapping);
	out_map->mapping = NULL;
	return -EINVAL;
}

static u16 unmap_class(struct selinux_map *map, u16 tclass)
{
	if (tclass < map->size)
		return map->mapping[tclass].value;

	return tclass;
}

static u16 map_class(struct selinux_map *map, u16 pol_value)
{
	u16 i;

	for (i = 1; i < map->size; i++) {
		if (map->mapping[i].value == pol_value)
			return i;
	}

	return SECCLASS_NULL;
}

static void map_decision(struct selinux_map *map,
			 u16 tclass, struct av_decision *avd,
			 int allow_unknown)
{
	if (tclass < map->size) {
		struct selinux_mapping *mapping = &map->mapping[tclass];
		unsigned int i, n = mapping->num_perms;
		u32 result;

		for (i = 0, result = 0; i < n; i++) {
			if (avd->allowed & mapping->perms[i])
				result |= 1<<i;
			if (allow_unknown && !mapping->perms[i])
				result |= 1<<i;
		}
		avd->allowed = result;

		for (i = 0, result = 0; i < n; i++)
			if (avd->auditallow & mapping->perms[i])
				result |= 1<<i;
		avd->auditallow = result;

		for (i = 0, result = 0; i < n; i++) {
			if (avd->auditdeny & mapping->perms[i])
				result |= 1<<i;
			if (!allow_unknown && !mapping->perms[i])
				result |= 1<<i;
		}
		for (; i < (sizeof(u32)*8); i++)
			result |= 1<<i;
		avd->auditdeny = result;
	}
}

int security_mls_enabled(struct selinux_state *state)
{
	struct policydb *p = &state->ss->policydb;

	return p->mls_enabled;
}

static int constraint_expr_eval(struct policydb *policydb,
				struct context *scontext,
				struct context *tcontext,
				struct context *xcontext,
				struct constraint_expr *cexpr)
{
	u32 val1, val2;
	struct context *c;
	struct role_datum *r1, *r2;
	struct mls_level *l1, *l2;
	struct constraint_expr *e;
	int s[CEXPR_MAXDEPTH];
	int sp = -1;

	for (e = cexpr; e; e = e->next) {
		switch (e->expr_type) {
		case CEXPR_NOT:
			BUG_ON(sp < 0);
			s[sp] = !s[sp];
			break;
		case CEXPR_AND:
			BUG_ON(sp < 1);
			sp--;
			s[sp] &= s[sp + 1];
			break;
		case CEXPR_OR:
			BUG_ON(sp < 1);
			sp--;
			s[sp] |= s[sp + 1];
			break;
		case CEXPR_ATTR:
			if (sp == (CEXPR_MAXDEPTH - 1))
				return 0;
			switch (e->attr) {
			case CEXPR_USER:
				val1 = scontext->user;
				val2 = tcontext->user;
				break;
			case CEXPR_TYPE:
				val1 = scontext->type;
				val2 = tcontext->type;
				break;
			case CEXPR_ROLE:
				val1 = scontext->role;
				val2 = tcontext->role;
				r1 = policydb->role_val_to_struct[val1 - 1];
				r2 = policydb->role_val_to_struct[val2 - 1];
				switch (e->op) {
				case CEXPR_DOM:
					s[++sp] = ebitmap_get_bit(&r1->dominates,
								  val2 - 1);
					continue;
				case CEXPR_DOMBY:
					s[++sp] = ebitmap_get_bit(&r2->dominates,
								  val1 - 1);
					continue;
				case CEXPR_INCOMP:
					s[++sp] = (!ebitmap_get_bit(&r1->dominates,
								    val2 - 1) &&
						   !ebitmap_get_bit(&r2->dominates,
								    val1 - 1));
					continue;
				default:
					break;
				}
				break;
			case CEXPR_L1L2:
				l1 = &(scontext->range.level[0]);
				l2 = &(tcontext->range.level[0]);
				goto mls_ops;
			case CEXPR_L1H2:
				l1 = &(scontext->range.level[0]);
				l2 = &(tcontext->range.level[1]);
				goto mls_ops;
			case CEXPR_H1L2:
				l1 = &(scontext->range.level[1]);
				l2 = &(tcontext->range.level[0]);
				goto mls_ops;
			case CEXPR_H1H2:
				l1 = &(scontext->range.level[1]);
				l2 = &(tcontext->range.level[1]);
				goto mls_ops;
			case CEXPR_L1H1:
				l1 = &(scontext->range.level[0]);
				l2 = &(scontext->range.level[1]);
				goto mls_ops;
			case CEXPR_L2H2:
				l1 = &(tcontext->range.level[0]);
				l2 = &(tcontext->range.level[1]);
				goto mls_ops;
mls_ops:
			switch (e->op) {
			case CEXPR_EQ:
				s[++sp] = mls_level_eq(l1, l2);
				continue;
			case CEXPR_NEQ:
				s[++sp] = !mls_level_eq(l1, l2);
				continue;
			case CEXPR_DOM:
				s[++sp] = mls_level_dom(l1, l2);
				continue;
			case CEXPR_DOMBY:
				s[++sp] = mls_level_dom(l2, l1);
				continue;
			case CEXPR_INCOMP:
				s[++sp] = mls_level_incomp(l2, l1);
				continue;
			default:
				BUG();
				return 0;
			}
			break;
			default:
				BUG();
				return 0;
			}

			switch (e->op) {
			case CEXPR_EQ:
				s[++sp] = (val1 == val2);
				break;
			case CEXPR_NEQ:
				s[++sp] = (val1 != val2);
				break;
			default:
				BUG();
				return 0;
			}
			break;
		case CEXPR_NAMES:
			if (sp == (CEXPR_MAXDEPTH-1))
				return 0;
			c = scontext;
			if (e->attr & CEXPR_TARGET)
				c = tcontext;
			else if (e->attr & CEXPR_XTARGET) {
				c = xcontext;
				if (!c) {
					BUG();
					return 0;
				}
			}
			if (e->attr & CEXPR_USER)
				val1 = c->user;
			else if (e->attr & CEXPR_ROLE)
				val1 = c->role;
			else if (e->attr & CEXPR_TYPE)
				val1 = c->type;
			else {
				BUG();
				return 0;
			}

			switch (e->op) {
			case CEXPR_EQ:
				s[++sp] = ebitmap_get_bit(&e->names, val1 - 1);
				break;
			case CEXPR_NEQ:
				s[++sp] = !ebitmap_get_bit(&e->names, val1 - 1);
				break;
			default:
				BUG();
				return 0;
			}
			break;
		default:
			BUG();
			return 0;
		}
	}

	BUG_ON(sp != 0);
	return s[0];
}

static int dump_masked_av_helper(void *k, void *d, void *args)
{
	struct perm_datum *pdatum = d;
	char **permission_names = args;

	BUG_ON(pdatum->value < 1 || pdatum->value > 32);

	permission_names[pdatum->value - 1] = (char *)k;

	return 0;
}

static void security_dump_masked_av(struct policydb *policydb,
				    struct context *scontext,
				    struct context *tcontext,
				    u16 tclass,
				    u32 permissions,
				    const char *reason)
{
	struct common_datum *common_dat;
	struct class_datum *tclass_dat;
	struct audit_buffer *ab;
	char *tclass_name;
	char *scontext_name = NULL;
	char *tcontext_name = NULL;
	char *permission_names[32];
	int index;
	u32 length;
	bool need_comma = false;

	if (!permissions)
		return;

	tclass_name = sym_name(policydb, SYM_CLASSES, tclass - 1);
	tclass_dat = policydb->class_val_to_struct[tclass - 1];
	common_dat = tclass_dat->comdatum;

	memset(permission_names, 0, sizeof(permission_names));

	if (common_dat &&
	    hashtab_map(common_dat->permissions.table,
			dump_masked_av_helper, permission_names) < 0)
		goto out;

	if (hashtab_map(tclass_dat->permissions.table,
			dump_masked_av_helper, permission_names) < 0)
		goto out;

	if (context_struct_to_string(policydb, scontext,
				     &scontext_name, &length) < 0)
		goto out;

	if (context_struct_to_string(policydb, tcontext,
				     &tcontext_name, &length) < 0)
		goto out;

	ab = audit_log_start(audit_context(),
			     GFP_ATOMIC, AUDIT_SELINUX_ERR);
	if (!ab)
		goto out;

	audit_log_format(ab, "op=security_compute_av reason=%s "
			 "scontext=%s tcontext=%s tclass=%s perms=",
			 reason, scontext_name, tcontext_name, tclass_name);

	for (index = 0; index < 32; index++) {
		u32 mask = (1 << index);

		if ((mask & permissions) == 0)
			continue;

		audit_log_format(ab, "%s%s",
				 need_comma ? "," : "",
				 permission_names[index]
				 ? permission_names[index] : "????");
		need_comma = true;
	}
	audit_log_end(ab);
out:
	kfree(tcontext_name);
	kfree(scontext_name);
}

static void type_attribute_bounds_av(struct policydb *policydb,
				     struct context *scontext,
				     struct context *tcontext,
				     u16 tclass,
				     struct av_decision *avd)
{
	struct context lo_scontext;
	struct context lo_tcontext, *tcontextp = tcontext;
	struct av_decision lo_avd;
	struct type_datum *source;
	struct type_datum *target;
	u32 masked = 0;

	source = flex_array_get_ptr(policydb->type_val_to_struct_array,
				    scontext->type - 1);
	BUG_ON(!source);

	if (!source->bounds)
		return;

	target = flex_array_get_ptr(policydb->type_val_to_struct_array,
				    tcontext->type - 1);
	BUG_ON(!target);

	memset(&lo_avd, 0, sizeof(lo_avd));

	memcpy(&lo_scontext, scontext, sizeof(lo_scontext));
	lo_scontext.type = source->bounds;

	if (target->bounds) {
		memcpy(&lo_tcontext, tcontext, sizeof(lo_tcontext));
		lo_tcontext.type = target->bounds;
		tcontextp = &lo_tcontext;
	}

	context_struct_compute_av(policydb, &lo_scontext,
				  tcontextp,
				  tclass,
				  &lo_avd,
				  NULL);

	masked = ~lo_avd.allowed & avd->allowed;

	if (likely(!masked))
		return;

	avd->allowed &= ~masked;

	security_dump_masked_av(policydb, scontext, tcontext,
				tclass, masked, "bounds");
}

void services_compute_xperms_drivers(
		struct extended_perms *xperms,
		struct avtab_node *node)
{
	unsigned int i;

	if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLDRIVER) {
		for (i = 0; i < ARRAY_SIZE(xperms->drivers.p); i++)
			xperms->drivers.p[i] |= node->datum.u.xperms->perms.p[i];
	} else if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLFUNCTION) {
		security_xperm_set(xperms->drivers.p,
					node->datum.u.xperms->driver);
	}

	if (node->key.specified & AVTAB_XPERMS_ALLOWED)
		xperms->len = 1;
}

static void context_struct_compute_av(struct policydb *policydb,
				      struct context *scontext,
				      struct context *tcontext,
				      u16 tclass,
				      struct av_decision *avd,
				      struct extended_perms *xperms)
{
	struct constraint_node *constraint;
	struct role_allow *ra;
	struct avtab_key avkey;
	struct avtab_node *node;
	struct class_datum *tclass_datum;
	struct ebitmap *sattr, *tattr;
	struct ebitmap_node *snode, *tnode;
	unsigned int i, j;

	avd->allowed = 0;
	avd->auditallow = 0;
	avd->auditdeny = 0xffffffff;
	if (xperms) {
		memset(&xperms->drivers, 0, sizeof(xperms->drivers));
		xperms->len = 0;
	}

	if (unlikely(!tclass || tclass > policydb->p_classes.nprim)) {
		if (printk_ratelimit())
			pr_warn("SELinux:  Invalid class %hu\n", tclass);
		return;
	}

	tclass_datum = policydb->class_val_to_struct[tclass - 1];

	avkey.target_class = tclass;
	avkey.specified = AVTAB_AV | AVTAB_XPERMS;
	sattr = flex_array_get(policydb->type_attr_map_array,
			       scontext->type - 1);
	BUG_ON(!sattr);
	tattr = flex_array_get(policydb->type_attr_map_array,
			       tcontext->type - 1);
	BUG_ON(!tattr);
	ebitmap_for_each_positive_bit(sattr, snode, i) {
		ebitmap_for_each_positive_bit(tattr, tnode, j) {
			avkey.source_type = i + 1;
			avkey.target_type = j + 1;
			for (node = avtab_search_node(&policydb->te_avtab,
						      &avkey);
			     node;
			     node = avtab_search_node_next(node, avkey.specified)) {
				if (node->key.specified == AVTAB_ALLOWED)
					avd->allowed |= node->datum.u.data;
				else if (node->key.specified == AVTAB_AUDITALLOW)
					avd->auditallow |= node->datum.u.data;
				else if (node->key.specified == AVTAB_AUDITDENY)
					avd->auditdeny &= node->datum.u.data;
				else if (xperms && (node->key.specified & AVTAB_XPERMS))
					services_compute_xperms_drivers(xperms, node);
			}

			cond_compute_av(&policydb->te_cond_avtab, &avkey,
					avd, xperms);

		}
	}

	constraint = tclass_datum->constraints;
	while (constraint) {
		if ((constraint->permissions & (avd->allowed)) &&
		    !constraint_expr_eval(policydb, scontext, tcontext, NULL,
					  constraint->expr)) {
			avd->allowed &= ~(constraint->permissions);
		}
		constraint = constraint->next;
	}

	if (tclass == policydb->process_class &&
	    (avd->allowed & policydb->process_trans_perms) &&
	    scontext->role != tcontext->role) {
		for (ra = policydb->role_allow; ra; ra = ra->next) {
			if (scontext->role == ra->role &&
			    tcontext->role == ra->new_role)
				break;
		}
		if (!ra)
			avd->allowed &= ~policydb->process_trans_perms;
	}

	type_attribute_bounds_av(policydb, scontext, tcontext,
				 tclass, avd);
}

static int security_validtrans_handle_fail(struct selinux_state *state,
					   struct context *ocontext,
					   struct context *ncontext,
					   struct context *tcontext,
					   u16 tclass)
{
	struct policydb *p = &state->ss->policydb;
	char *o = NULL, *n = NULL, *t = NULL;
	u32 olen, nlen, tlen;

	if (context_struct_to_string(p, ocontext, &o, &olen))
		goto out;
	if (context_struct_to_string(p, ncontext, &n, &nlen))
		goto out;
	if (context_struct_to_string(p, tcontext, &t, &tlen))
		goto out;
	audit_log(audit_context(), GFP_ATOMIC, AUDIT_SELINUX_ERR,
		  "op=security_validate_transition seresult=denied"
		  " oldcontext=%s newcontext=%s taskcontext=%s tclass=%s",
		  o, n, t, sym_name(p, SYM_CLASSES, tclass-1));
out:
	kfree(o);
	kfree(n);
	kfree(t);

	if (!enforcing_enabled(state))
		return 0;
	return -EPERM;
}

static int security_compute_validatetrans(struct selinux_state *state,
					  u32 oldsid, u32 newsid, u32 tasksid,
					  u16 orig_tclass, bool user)
{
	struct policydb *policydb;
	struct sidtab *sidtab;
	struct context *ocontext;
	struct context *ncontext;
	struct context *tcontext;
	struct class_datum *tclass_datum;
	struct constraint_node *constraint;
	u16 tclass;
	int rc = 0;


	if (!state->initialized)
		return 0;

	read_lock(&state->ss->policy_rwlock);

	policydb = &state->ss->policydb;
	sidtab = state->ss->sidtab;

	if (!user)
		tclass = unmap_class(&state->ss->map, orig_tclass);
	else
		tclass = orig_tclass;

	if (!tclass || tclass > policydb->p_classes.nprim) {
		rc = -EINVAL;
		goto out;
	}
	tclass_datum = policydb->class_val_to_struct[tclass - 1];

	ocontext = sidtab_search(sidtab, oldsid);
	if (!ocontext) {
		pr_err("SELinux: %s:  unrecognized SID %d\n",
			__func__, oldsid);
		rc = -EINVAL;
		goto out;
	}

	ncontext = sidtab_search(sidtab, newsid);
	if (!ncontext) {
		pr_err("SELinux: %s:  unrecognized SID %d\n",
			__func__, newsid);
		rc = -EINVAL;
		goto out;
	}

	tcontext = sidtab_search(sidtab, tasksid);
	if (!tcontext) {
		pr_err("SELinux: %s:  unrecognized SID %d\n",
			__func__, tasksid);
		rc = -EINVAL;
		goto out;
	}

	constraint = tclass_datum->validatetrans;
	while (constraint) {
		if (!constraint_expr_eval(policydb, ocontext, ncontext,
					  tcontext, constraint->expr)) {
			if (user)
				rc = -EPERM;
			else
				rc = security_validtrans_handle_fail(state,
								     ocontext,
								     ncontext,
								     tcontext,
								     tclass);
			goto out;
		}
		constraint = constraint->next;
	}

out:
	read_unlock(&state->ss->policy_rwlock);
	return rc;
}

int security_validate_transition_user(struct selinux_state *state,
				      u32 oldsid, u32 newsid, u32 tasksid,
				      u16 tclass)
{
	return security_compute_validatetrans(state, oldsid, newsid, tasksid,
					      tclass, true);
}

int security_validate_transition(struct selinux_state *state,
				 u32 oldsid, u32 newsid, u32 tasksid,
				 u16 orig_tclass)
{
	return security_compute_validatetrans(state, oldsid, newsid, tasksid,
					      orig_tclass, false);
}

int security_bounded_transition(struct selinux_state *state,
				u32 old_sid, u32 new_sid)
{
	struct policydb *policydb;
	struct sidtab *sidtab;
	struct context *old_context, *new_context;
	struct type_datum *type;
	int index;
	int rc;

	if (!state->initialized)
		return 0;

	read_lock(&state->ss->policy_rwlock);

	policydb = &state->ss->policydb;
	sidtab = state->ss->sidtab;

	rc = -EINVAL;
	old_context = sidtab_search(sidtab, old_sid);
	if (!old_context) {
		pr_err("SELinux: %s: unrecognized SID %u\n",
		       __func__, old_sid);
		goto out;
	}

	rc = -EINVAL;
	new_context = sidtab_search(sidtab, new_sid);
	if (!new_context) {
		pr_err("SELinux: %s: unrecognized SID %u\n",
		       __func__, new_sid);
		goto out;
	}

	rc = 0;
	if (old_context->type == new_context->type)
		goto out;

	index = new_context->type;
	while (true) {
		type = flex_array_get_ptr(policydb->type_val_to_struct_array,
					  index - 1);
		BUG_ON(!type);

		rc = -EPERM;
		if (!type->bounds)
			break;

		rc = 0;
		if (type->bounds == old_context->type)
			break;

		index = type->bounds;
	}

	if (rc) {
		char *old_name = NULL;
		char *new_name = NULL;
		u32 length;

		if (!context_struct_to_string(policydb, old_context,
					      &old_name, &length) &&
		    !context_struct_to_string(policydb, new_context,
					      &new_name, &length)) {
			audit_log(audit_context(),
				  GFP_ATOMIC, AUDIT_SELINUX_ERR,
				  "op=security_bounded_transition "
				  "seresult=denied "
				  "oldcontext=%s newcontext=%s",
				  old_name, new_name);
		}
		kfree(new_name);
		kfree(old_name);
	}
out:
	read_unlock(&state->ss->policy_rwlock);

	return rc;
}

static void avd_init(struct selinux_state *state, struct av_decision *avd)
{
	avd->allowed = 0;
	avd->auditallow = 0;
	avd->auditdeny = 0xffffffff;
	avd->seqno = state->ss->latest_granting;
	avd->flags = 0;
}

void services_compute_xperms_decision(struct extended_perms_decision *xpermd,
					struct avtab_node *node)
{
	unsigned int i;

	if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLFUNCTION) {
		if (xpermd->driver != node->datum.u.xperms->driver)
			return;
	} else if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLDRIVER) {
		if (!security_xperm_test(node->datum.u.xperms->perms.p,
					xpermd->driver))
			return;
	} else {
		BUG();
	}

	if (node->key.specified == AVTAB_XPERMS_ALLOWED) {
		xpermd->used |= XPERMS_ALLOWED;
		if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLDRIVER) {
			memset(xpermd->allowed->p, 0xff,
					sizeof(xpermd->allowed->p));
		}
		if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLFUNCTION) {
			for (i = 0; i < ARRAY_SIZE(xpermd->allowed->p); i++)
				xpermd->allowed->p[i] |=
					node->datum.u.xperms->perms.p[i];
		}
	} else if (node->key.specified == AVTAB_XPERMS_AUDITALLOW) {
		xpermd->used |= XPERMS_AUDITALLOW;
		if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLDRIVER) {
			memset(xpermd->auditallow->p, 0xff,
					sizeof(xpermd->auditallow->p));
		}
		if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLFUNCTION) {
			for (i = 0; i < ARRAY_SIZE(xpermd->auditallow->p); i++)
				xpermd->auditallow->p[i] |=
					node->datum.u.xperms->perms.p[i];
		}
	} else if (node->key.specified == AVTAB_XPERMS_DONTAUDIT) {
		xpermd->used |= XPERMS_DONTAUDIT;
		if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLDRIVER) {
			memset(xpermd->dontaudit->p, 0xff,
					sizeof(xpermd->dontaudit->p));
		}
		if (node->datum.u.xperms->specified == AVTAB_XPERMS_IOCTLFUNCTION) {
			for (i = 0; i < ARRAY_SIZE(xpermd->dontaudit->p); i++)
				xpermd->dontaudit->p[i] |=
					node->datum.u.xperms->perms.p[i];
		}
	} else {
		BUG();
	}
}

void security_compute_xperms_decision(struct selinux_state *state,
				      u32 ssid,
				      u32 tsid,
				      u16 orig_tclass,
				      u8 driver,
				      struct extended_perms_decision *xpermd)
{
	struct policydb *policydb;
	struct sidtab *sidtab;
	u16 tclass;
	struct context *scontext, *tcontext;
	struct avtab_key avkey;
	struct avtab_node *node;
	struct ebitmap *sattr, *tattr;
	struct ebitmap_node *snode, *tnode;
	unsigned int i, j;

	xpermd->driver = driver;
	xpermd->used = 0;
	memset(xpermd->allowed->p, 0, sizeof(xpermd->allowed->p));
	memset(xpermd->auditallow->p, 0, sizeof(xpermd->auditallow->p));
	memset(xpermd->dontaudit->p, 0, sizeof(xpermd->dontaudit->p));

	read_lock(&state->ss->policy_rwlock);
	if (!state->initialized)
		goto allow;

	policydb = &state->ss->policydb;
	sidtab = state->ss->sidtab;

	scontext = sidtab_search(sidtab, ssid);
	if (!scontext) {
		pr_err("SELinux: %s: unrecognized SID %d\n", __func__, ssid);
		goto out;
	}
	tcontext = sidtab_search(sidtab, tsid);
	if (!tcontext) {
		pr_err("SELinux: %s: unrecognized SID %d\n", __func__, tsid);
		goto out;
	}

	tclass = unmap_class(&state->ss->map, orig_tclass);
	if (unlikely(orig_tclass && !tclass)) {
		if (policydb->allow_unknown)
			goto allow;
		goto out;
	}

	if (unlikely(!tclass || tclass > policydb->p_classes.nprim)) {
		pr_warn_ratelimited("SELinux: Invalid class %hu\n", tclass);
		goto out;
	}

	avkey.target_class = tclass;
	avkey.specified = AVTAB_XPERMS;
	sattr = flex_array_get(policydb->type_attr_map_array, scontext->type - 1);
	BUG_ON(!sattr);
	tattr = flex_array_get(policydb->type_attr_map_array, tcontext->type - 1);
	BUG_ON(!tattr);
	ebitmap_for_each_positive_bit(sattr, snode, i) {
		ebitmap_for_each_positive_bit(tattr, tnode, j) {
			avkey.source_type = i + 1;
			avkey.target_type = j + 1;
			for (node = avtab_search_node(&policydb->te_avtab, &avkey); node; node = avtab_search_node_next(node, avkey.specified))
				services_compute_xperms_decision(xpermd, node);
			cond_compute_xperms(&policydb->te_cond_avtab, &avkey, xpermd);
		}
	}
out:
	read_unlock(&state->ss->policy_rwlock);
	return;
allow:
	memset(xpermd->allowed->p, 0xff, sizeof(xpermd->allowed->p));
	goto out;
}

void security_compute_av(struct selinux_state *state, u32 ssid, u32 tsid, u16 orig_tclass, struct av_decision *avd, struct extended_perms *xperms)
{
	struct policydb *policydb;
	struct sidtab *sidtab;
	u16 tclass;
	struct context *scontext = NULL, *tcontext = NULL;

	read_lock(&state->ss->policy_rwlock);
	avd_init(state, avd);
	xperms->len = 0;
	if (!state->initialized)
		goto allow;

	policydb = &state->ss->policydb;
	sidtab = state->ss->sidtab;

	scontext = sidtab_search(sidtab, ssid);
	if (!scontext) {
		pr_err("SELinux: %s: unrecognized SID %d\n", __func__, ssid);
		goto out;
	}

	if (ebitmap_get_bit(&policydb->permissive_map, scontext->type))
		avd->flags |= AVD_FLAGS_PERMISSIVE;

	tcontext = sidtab_search(sidtab, tsid);
	if (!tcontext) {
		pr_err("SELinux: %s: unrecognized SID %d\n", __func__, tsid);
		goto out;
	}

	tclass = unmap_class(&state->ss->map, orig_tclass);
	if (unlikely(orig_tclass && !tclass)) {
		if (policydb->allow_unknown)
			goto allow;
		goto out;
	}

	context_struct_compute_av(policydb, scontext, tcontext, tclass, avd, xperms);
	map_decision(&state->ss->map, orig_tclass, avd, policydb->allow_unknown);
out:
	read_unlock(&state->ss->policy_rwlock);
	return;
allow:
	avd->allowed = 0xffffffff;
	goto out;
}

void security_compute_av_user(struct selinux_state *state, u32 ssid, u32 tsid, u16 tclass, struct av_decision *avd)
{
	struct policydb *policydb;
	struct sidtab *sidtab;
	struct context *scontext = NULL, *tcontext = NULL;

	read_lock(&state->ss->policy_rwlock);
	avd_init(state, avd);
	if (!state->initialized)
		goto allow;

	policydb = &state->ss->policydb;
	sidtab = state->ss->sidtab;

	scontext = sidtab_search(sidtab, ssid);
	if (!scontext) {
		pr_err("SELinux: %s: unrecognized SID %d\n", __func__, ssid);
		goto out;
	}

	if (ebitmap_get_bit(&policydb->permissive_map, scontext->type))
		avd->flags |= AVD_FLAGS_PERMISSIVE;

	tcontext = sidtab_search(sidtab, tsid);
	if (!tcontext) {
		pr_err("SELinux: %s: unrecognized SID %d\n", __func__, tsid);
		goto out;
	}

	if (unlikely(!tclass)) {
		if (policydb->allow_unknown)
			goto allow;
		goto out;
	}

	context_struct_compute_av(policydb, scontext, tcontext, tclass, avd, NULL);
out:
	read_unlock(&state->ss->policy_rwlock);
	return;
allow:
	avd->allowed = 0xffffffff;
	goto out;
}

static int context_struct_to_string(struct policydb *p, struct context *context, char **scontext, u32 *scontext_len)
{
	char *scontextp;

	if (scontext)
		*scontext = NULL;
	*scontext_len = 0;

	if (context->len) {
		*scontext_len = context->len;
		if (scontext) {
			*scontext = kstrdup(context->str, GFP_ATOMIC);
			if (!(*scontext))
				return -ENOMEM;
		}
		return 0;
	}

	*scontext_len += strlen(sym_name(p, SYM_USERS, context->user - 1)) + 1;
	*scontext_len += strlen(sym_name(p, SYM_ROLES, context->role - 1)) + 1;
	*scontext_len += strlen(sym_name(p, SYM_TYPES, context->type - 1)) + 1;
	*scontext_len += mls_compute_context_len(p, context);

	if (!scontext)
		return 0;

	*scontext = kmalloc(*scontext_len, GFP_ATOMIC);
	if (!(*scontext))
		return -ENOMEM;

	scontextp = *scontext;

	sprintf(scontextp, "%s:%s:%s",
		sym_name(p, SYM_USERS, context->user - 1),
		sym_name(p, SYM_ROLES, context->role - 1),
		sym_name(p, SYM_TYPES, context->type - 1));
	scontextp += strlen(scontextp);

	mls_append_to_context(p, context, &scontextp);

	return 0;
}

int security_sid_to_context(struct selinux_state *state, u32 sid,
			    char **scontext, u32 *scontext_len)
{
	struct context *context;
	int rc;

	if (!state->initialized) {
		if (sid <= SECINITSID_NUM) {
			char *initial_sid_to_string[] = {
				NULL,
				"kernel",
				"security",
				"unlabeled",
				"fs",
				"file",
				"file_labels",
				"init",
				"kernel",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
				"unlabeled",
			};
			*scontext_len = strlen(initial_sid_to_string[sid]) + 1;
			*scontext = kstrdup(initial_sid_to_string[sid], GFP_ATOMIC);
			if (!(*scontext))
				return -ENOMEM;
			return 0;
		}
		return -EINVAL;
	}

	read_lock(&state->ss->policy_rwlock);
	context = sidtab_search(state->ss->sidtab, sid);
	if (!context) {
		pr_err("SELinux: %s:  unrecognized SID %d\n",
			__func__, sid);
		rc = -EINVAL;
		goto out;
	}
	rc = context_struct_to_string(&state->ss->policydb, context, scontext, scontext_len);
out:
	read_unlock(&state->ss->policy_rwlock);
	return rc;

}

int security_sid_to_context_force(struct selinux_state *state, u32 sid,
				  char **scontext, u32 *scontext_len)
{
	return security_sid_to_context(state, sid, scontext, scontext_len);
}

int security_context_to_sid(struct selinux_state *state, const char *scontext,
			    u32 scontext_len, u32 *sid, gfp_t gfp)
{
	return security_context_to_sid_core(state, scontext, scontext_len,
					   sid, SECSID_NULL, gfp, 0);
}

int security_context_to_sid_force(struct selinux_state *state,
				  const char *scontext, u32 scontext_len,
				  u32 *sid)
{
	return security_context_to_sid_core(state, scontext, scontext_len,
					   sid, SECSID_NULL, GFP_ATOMIC, 1);
}

static int security_compute_sid(struct selinux_state *state,
				u32 ssid,
				u32 tsid,
				u16 orig_tclass,
				u32 specified,
				u32 *out_sid,
				bool kern)
{
	struct policydb *policydb;
	struct sidtab *sidtab;
	struct class_datum *tclass_datum;
	struct context *scontext = NULL, *tcontext = NULL, newcontext;
	struct role_trans *roletr = NULL;
	struct avtab_key avkey;
	struct avtab_node *node;
	struct ebitmap_node *snode, *tnode;
	unsigned int i, j;
	u16 tclass;
	int rc = 0;

	if (!state->initialized) {
		switch (orig_tclass) {
		case SECCLASS_PROCESS:
			*out_sid = ssid;
			break;
		default:
			*out_sid = tsid;
			break;
		}
		goto out;
	}

	context_init(&newcontext);

	read_lock(&state->ss->policy_rwlock);

	policydb = &state->ss->policydb;
	sidtab = state->ss->sidtab;

	scontext = sidtab_search(sidtab, ssid);
	if (!scontext) {
		pr_err("SELinux: %s:  unrecognized SID %d\n",
		       __func__, ssid);
		rc = -EINVAL;
		goto out_unlock;
	}
	tcontext = sidtab_search(sidtab, tsid);
	if (!tcontext) {
		pr_err("SELinux: %s:  unrecognized SID %d\n",
		       __func__, tsid);
		rc = -EINVAL;
		goto out_unlock;
	}

	if (kern)
		tclass = unmap_class(&state->ss->map, orig_tclass);
	else
		tclass = orig_tclass;

	if (!tclass || tclass > policydb->p_classes.nprim) {
		pr_err("SELinux:  unrecognized class %d\n", tclass);
		rc = -EINVAL;
		goto out_unlock;
	}

	tclass_datum = policydb->class_val_to_struct[tclass - 1];

	newcontext.user = scontext->user;
	newcontext.role = scontext->role;
	newcontext.type = scontext->type;

	memcpy(&newcontext.range, &scontext->range, sizeof(newcontext.range));

	if (specified & AVTAB_TRANSITION) {
		avkey.source_type = scontext->type;
		avkey.target_type = tcontext->type;
		avkey.target_class = tclass;
		avkey.specified = AVTAB_TRANSITION;
		node = avtab_search_node(&policydb->te_avtab, &avkey);
		if (node) {
			newcontext.type = node->datum.u.data;
		} else {
			struct ebitmap *sattr, *tattr;

			sattr = flex_array_get(policydb->type_attr_map_array, scontext->type - 1);
			tattr = flex_array_get(policydb->type_attr_map_array, tcontext->type - 1);
			ebitmap_for_each_positive_bit(sattr, snode, i) {
				ebitmap_for_each_positive_bit(tattr, tnode, j) {
					avkey.source_type = i + 1;
					avkey.target_type = j + 1;
					node = avtab_search_node(&policydb->te_avtab, &avkey);
					if (node) {
						newcontext.type = node->datum.u.data;
						goto found_te;
					}
				}
			}
		}
	}
found_te:
	if (specified & AVTAB_MEMBER) {
		avkey.source_type = scontext->type;
		avkey.target_type = tcontext->type;
		avkey.target_class = tclass;
		avkey.specified = AVTAB_MEMBER;
		node = avtab_search_node(&policydb->te_avtab, &avkey);
		if (node)
			newcontext.type = node->datum.u.data;
	}

	if (specified & AVTAB_CHANGE) {
		avkey.source_type = scontext->type;
		avkey.target_type = tcontext->type;
		avkey.target_class = tclass;
		avkey.specified = AVTAB_CHANGE;
		node = avtab_search_node(&policydb->te_avtab, &avkey);
		if (node)
			newcontext.type = node->datum.u.data;
	}

	if (specified & AVTAB_TRANSITION) {
		for (roletr = policydb->role_tr; roletr; roletr = roletr->next) {
			if (roletr->role == scontext->role &&
			    roletr->type == tcontext->type &&
			    roletr->tclass == tclass) {
				newcontext.role = roletr->new_role;
				break;
			}
		}
	}

	mls_compute_sid(policydb, scontext, tcontext, tclass, specified, &newcontext);

	rc = context_struct_to_sid(policydb, sidtab, &newcontext, out_sid);
out_unlock:
	read_unlock(&state->ss->policy_rwlock);
	context_destroy(&newcontext);
out:
	return rc;
}

int security_transition_sid(struct selinux_state *state, u32 ssid, u32 tsid,
			    u16 tclass, const struct qstr *objname, u32 *out_sid)
{
	return security_compute_sid(state, ssid, tsid, tclass, AVTAB_TRANSITION,
				    out_sid, false);
}

int security_member_sid(struct selinux_state *state, u32 ssid, u32 tsid,
			u16 tclass, u32 *out_sid)
{
	return security_compute_sid(state, ssid, tsid, tclass, AVTAB_MEMBER,
				    out_sid, false);
}

int security_change_sid(struct selinux_state *state, u32 ssid, u32 tsid,
			u16 tclass, u32 *out_sid)
{
	return security_compute_sid(state, ssid, tsid, tclass, AVTAB_CHANGE,
				    out_sid, false);
}

#ifdef CONFIG_NETLABEL
int security_netlbl_sid_to_secattr(struct selinux_state *state,
				   u32 sid, struct netlbl_lsm_secattr *secattr)
{
	struct policydb *policydb = &state->ss->policydb;
	int rc;
	struct context *ctx;

	if (!state->initialized)
		return 0;

	read_lock(&state->ss->policy_rwlock);

	rc = -ENOENT;
	ctx = sidtab_search(state->ss->sidtab, sid);
	if (ctx == NULL)
		goto out;

	rc = -ENOMEM;
	secattr->domain = kstrdup(sym_name(policydb, SYM_TYPES, ctx->type - 1),
				  GFP_ATOMIC);
	if (secattr->domain == NULL)
		goto out;

	secattr->attr.secid = sid;
	secattr->flags |= NETLBL_SECATTR_DOMAIN_CPY | NETLBL_SECATTR_SECID;
	mls_export_netlbl_lvl(policydb, ctx, secattr);
	rc = mls_export_netlbl_cat(policydb, ctx, secattr);
out:
	read_unlock(&state->ss->policy_rwlock);
	return rc;
}
#endif
