/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*          Xavier Leroy and Damien Doligez, INRIA Rocquencourt           */
/*                                                                        */
/*   Copyright 1996 Institut National de Recherche en Informatique et     */
/*     en Automatique.                                                    */
/*                                                                        */
/*   All rights reserved.  This file is distributed under the terms of    */
/*   the GNU Lesser General Public License version 2.1, with the          */
/*   special exception on linking described in the file LICENSE.          */
/*                                                                        */
/**************************************************************************/

#define VERIMAG_MEASUREMENTS
#define CAML_INTERNALS

/* Main entry point (can be overridden by a user-provided main()
   function that calls caml_main() later). */

#include "caml/misc.h"
#include "caml/mlvalues.h"
#include "caml/sys.h"
#include "caml/osdeps.h"
#ifdef _WIN32
#include <windows.h>
#endif

#ifdef VERIMAG_MEASUREMENTS
#include "../../clock.h"
#endif

CAMLextern void caml_main (char_os **);

#ifdef _WIN32
CAMLextern void caml_expand_command_line (int *, wchar_t ***);

int wmain(int argc, wchar_t **argv)
#else
int main(int argc, char **argv)
#endif
{
#ifdef _WIN32
  /* Expand wildcards and diversions in command line */
  caml_expand_command_line(&argc, &argv);
#endif

#ifdef VERIMAG_MEASUREMENTS
  clock_prepare();
  clock_start();
#endif
  caml_main(argv);
#ifdef VERIMAG_MEASUREMENTS
  clock_stop();
  print_total_clock();
#endif
  caml_sys_exit(Val_int(0));
  return 0; /* not reached */
}
