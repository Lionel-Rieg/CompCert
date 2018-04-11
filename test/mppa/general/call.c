int sum(int a, int b){
    return a + b;
}

int make_42(void){
    return 42;
}

int make_18(void){
    return 18;
}

int main(void){
    return sum(make_42(), make_18());
    //return make_42() + make_18();
}

/* RETURN VALUE: 60 */
