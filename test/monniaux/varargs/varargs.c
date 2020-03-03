#include <stdio.h>
#include <stdarg.h>

void simple_printf(const char* fmt, ...)
{
    va_list args;
    va_start(args, fmt);
 
    while (*fmt != '\0') {
        if (*fmt == 'd') {
            int i = va_arg(args, int);
            printf("%d\n", i);
        } else if (*fmt == 'c') {
            // A 'char' variable will be promoted to 'int'
            // A character literal in C is already 'int' by itself
            int c = va_arg(args, int);
            printf("%c\n", c);
        } else if (*fmt == 'f') {
            double d = va_arg(args, double);
            printf("%f\n", d);
        } else if (*fmt == 'l') {
            long d = va_arg(args, long);
            printf("%ld\n", d);
        }
        ++fmt;
    }
 
    va_end(args);
}
 
int main(void)
{
  simple_printf("dlcff", 3, 4L, 'a', 1.999, 42.5); 
}
