#include "framework.h"

int sum(int a, int b){
    return a+b;
}

int make(int a){
    return a;
}

BEGIN_TEST(int)
{
    c = sum(make(a), make(b));
}
END_TEST32()
/* RETURN VALUE: 60 */
