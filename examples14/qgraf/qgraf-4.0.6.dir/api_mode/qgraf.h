
//  this file is part of qgraf-4.0.6


   typedef struct qisgnls_ty {
    int_least32_t init;
    int_least32_t msg_count;
    int_least32_t count;
    int_least32_t stop;
    int_least32_t prologue;
    int_least32_t diagram;
    int_least32_t epilogue;
    int_least32_t hold;
    int_least32_t elinks;
    int_least32_t topology;
    int_least32_t partition;
    int_least32_t loops;
    int_least32_t y;
    int_least32_t n;
   } qisgnls ;

   const qisgnls qisgnl = { -9, -10, -11, -12, -13, -14, -15, -16, -17, -18, -19, -20, -21, -22 };

   typedef struct qrsgnls_ty {
    int_least32_t ok;
    int_least32_t end;
    int_least32_t input_error;
    int_least32_t q_error;
    int_least32_t os_error;
   } qrsgnls ;

   const qrsgnls qrsgnl = { -2, -3, -4, -5, -6 };


#define  CCS_L0  46080

#define  A_SIZE  7


#ifdef __cplusplus
 extern "C" {
#endif

#ifdef Q_F2008
   void qinterf2008c( int_least32_t *arg1, int_least32_t *arg2, char *arg3, int_least32_t *arg4, int_least64_t *arg5 );
#endif

#ifdef Q_F2018
   void qinterf2018c( int_least32_t *arg1, int_least32_t *arg2, CFI_cdesc_t *arg3, int_least32_t *arg4,
      int_least64_t *arg5 );
#endif

#ifdef __cplusplus
}
#endif

