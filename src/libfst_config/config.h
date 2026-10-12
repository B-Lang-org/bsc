/* Configuration for building libfst (the src/vendor/libfst submodule)
 * into the Bluesim kernel library.  fstapi.c includes <config.h>; the
 * knobs it consults are listed in the submodule's meson.build.
 *
 * HAVE_LIBPTHREAD / FST_WRITER_PARALLEL are deliberately left
 * undefined: Bluesim uses the writer single-threaded.
 */

#define HAVE_FSEEKO 1
#define HAVE_REALPATH 1
