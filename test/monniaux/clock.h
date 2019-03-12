typedef unsigned long cycle_t;

void clock_prepare(void);
void clock_stop(void);
void clock_start(void);
cycle_t get_total_clock(void);
cycle_t get_current_cycle(void);
void print_total_clock(void);
void printerr_total_clock(void);
