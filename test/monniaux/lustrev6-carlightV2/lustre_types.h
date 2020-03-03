/* This file was generated by lv6 version master.737 (2727a7744111c84f7984634d2bd3ad6f7c6c7ff9). */
/*  lv6 carlightV2.lus -n carlight --to-c */
/* on vanoise the 08/05/2019 at 22:54:09 */

#ifndef _SOC2C_PREDEF_TYPES
#define _SOC2C_PREDEF_TYPES
typedef int _boolean;
typedef int _integer;
typedef char* _string;
typedef double _real;
typedef double _double;
typedef float _float;
#define _false 0
#define _true 1
#endif
// end of _SOC2C_PREDEF_TYPES
// User typedef 
#ifndef _carlightV2_carlight_TYPES
#define _carlightV2_carlight_TYPES
typedef _integer carlightV2_SwitchMode;
#endif // enf of  _carlightV2_carlight_TYPES
// Memoryless soc ctx typedef 
// Memoryfull soc ctx typedef 
/* Lustre_pre_ctx */
typedef struct {
   /*Memory cell*/
   _boolean _memory ;
} Lustre_pre_ctx_type;

/* Lustre_arrow_ctx */
typedef struct {
   /*Memory cell*/
   _boolean _memory ;
} Lustre_arrow_ctx_type;

/* carlightV2_front_montant_ctx */
typedef struct {
   /*INSTANCES*/
   Lustre_pre_ctx_type Lustre_pre_ctx_tab[1];
   Lustre_arrow_ctx_type Lustre_arrow_ctx_tab[1];
} carlightV2_front_montant_ctx_type;

/* Lustre_pre_2_ctx */
typedef struct {
   /*Memory cell*/
   _real _memory ;
} Lustre_pre_2_ctx_type;

/* Lustre_arrow_2_ctx */
typedef struct {
   /*Memory cell*/
   _boolean _memory ;
} Lustre_arrow_2_ctx_type;

/* carlightV2_vrai_depuis_n_secondes_ctx */
typedef struct {
   /*INSTANCES*/
   Lustre_pre_2_ctx_type Lustre_pre_2_ctx_tab[1];
   Lustre_arrow_2_ctx_type Lustre_arrow_2_ctx_tab[1];
} carlightV2_vrai_depuis_n_secondes_ctx_type;

/* carlightV2_carlight_auto_ctx */
typedef struct {
   /*INSTANCES*/
   carlightV2_vrai_depuis_n_secondes_ctx_type carlightV2_vrai_depuis_n_secondes_ctx_tab[2];
} carlightV2_carlight_auto_ctx_type;

/* carlightV2_carlight_ctx */
typedef struct {
   /*INSTANCES*/
   carlightV2_front_montant_ctx_type carlightV2_front_montant_ctx_tab[1];
   carlightV2_carlight_auto_ctx_type carlightV2_carlight_auto_ctx_tab[1];
   Lustre_pre_ctx_type Lustre_pre_ctx_tab[1];
} carlightV2_carlight_ctx_type;

