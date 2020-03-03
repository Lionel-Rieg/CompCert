typedef double op_int_double(int, double);
typedef float op_int_float(int, float);

double send_through_double(op_int_double f, int x, int y, double z);
float send_through_float(op_int_float f, int x, int y, float z);
void print_from_ccomp(double x);
