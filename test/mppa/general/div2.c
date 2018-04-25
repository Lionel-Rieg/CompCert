#define SIZE 10

int main(void){
    int a[SIZE], b[SIZE], c[SIZE];
    int i;

    for (i = 0 ; i < SIZE ; i++){
        a[i] = i-5;
        b[i] = -i+2;
        c[i] = (a[i] + b[i]) / 2;
    }
    /* a = {-5, -4, .., 5}
     * b = { 2,  1, .., -8}
     */

    for (i = 0 ; i < SIZE ; i++)
        if (c[i] != -1)
            return c[i];

    return 42;
}
/* RETURN VALUE: 42 */
