#ifndef __CCOMP_KIC_FIXES_H
#define __CCOMP_KIC_FIXES_H

#undef __GNUC__
#define __thread

struct __int128_ccomp { long __int128_ccomp_low; long __int128_ccomp_high; };

#define __int128 struct __int128_ccomp

#endif
