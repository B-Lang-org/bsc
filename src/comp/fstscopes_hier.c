/* Flat C accessors for libfst's fstHier record, for use from
 * fstscopes.hs via the FFI: the record contains a union, which the
 * Haskell FFI cannot portably access without a helper.
 */

#include <stdlib.h>

#include "fstapi.h"

/* 0 = scope, 1 = upscope, 2 = var, 3 = anything else */
int bsc_fsthier_kind(struct fstHier *h)
{
    switch (h->htyp) {
    case FST_HT_SCOPE:   return 0;
    case FST_HT_UPSCOPE: return 1;
    case FST_HT_VAR:     return 2;
    default:             return 3;
    }
}

const char *bsc_fsthier_scope_name(struct fstHier *h)
{
    return h->u.scope.name;
}

/* NULL when the scope has no component (module type) recorded */
const char *bsc_fsthier_scope_component(struct fstHier *h)
{
    return (h->u.scope.component_length > 0) ? h->u.scope.component : NULL;
}

const char *bsc_fsthier_var_name(struct fstHier *h)
{
    return h->u.var.name;
}

unsigned bsc_fsthier_var_length(struct fstHier *h)
{
    return h->u.var.length;
}

unsigned bsc_fsthier_var_handle(struct fstHier *h)
{
    return h->u.var.handle;
}

int bsc_fsthier_var_is_alias(struct fstHier *h)
{
    return h->u.var.is_alias;
}
