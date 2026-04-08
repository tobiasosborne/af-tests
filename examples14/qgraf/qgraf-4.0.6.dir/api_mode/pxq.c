

#include <memory.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "ISO_Fortran_binding.h"
#include "qgraf.h"




 int main()
{

   int_least32_t  maxlen[A_SIZE], csl[A_SIZE];

   int_least32_t  s1, s2 ;

   int_least64_t  lintc, k1 ;

   int  ij, stylefiles, cfi_stat ;

   char  ccs[CCS_L0];

   char  *ccs1[A_SIZE];

   int  c1 ;

   CFI_CDESC_T(0)  ccsf ;

   FILE *fout1, *fout2 ;


/*   void  qinterf2018c;  */


   maxlen[0] = (int_least32_t) 4096 ;
   maxlen[1] = (int_least32_t) 2048 ;


/*  create CFI descriptor for string ccs  */

   cfi_stat = CFI_establish((CFI_cdesc_t *)&ccsf, (CFI_cdesc_t *)&ccs,
                 CFI_attribute_pointer, CFI_type_char, 1, 0, NULL);

   printf("\n  cfi_status is now  %d\n", cfi_stat);



/*  some basic definitions  */


   stylefiles = 2 ;

   csl[0] = maxlen[0];
   csl[1] = maxlen[1];


/*  open two output files (for testing) */


   fout1 = fopen("out_tmp/pxq_out1","w");
   fout2 = fopen("out_tmp/pxq_out2","w");


/*  compute offsets  */
/*  size of char is assumed to be 1  */


   ccs1[0] = ccs ;
   ij = 1 ;
   while ( ij < stylefiles ) {
      ccs1[ij]= ccs1[ij-1] +csl[ij-1];
      ij++ ;
   }


/*  initialize qgraf  */
/*  call Fortran to print onto the string  */

   memcpy(ccs1[0],"'q_api.dat'\0",12);

   s1 = qisgnl.init ;
   s2 = qrsgnl.ok ;

   lintc = (int_least64_t) CCS_L0 ;

   qinterf2018c(&s1,&s2,(CFI_cdesc_t *)&ccsf,csl,&lintc);

/*   cfi_stat = CFI_deallocate((CFI_cdesc_t *)&ccsf);  */

   if ( s2 != qrsgnl.ok ) {
      printf("\n error_message:  %s\n\n", ccs1[0]);
      exit(1);
   }

   if ( lintc != (int_least64_t) stylefiles ) {
      printf("\n there was a problem with the initialization\n");
      printf("\n    stylefiles is  %d\n\n", stylefiles);
      printf("\n    lintc is  %d\n\n", lintc);
      exit(1);
   }


   printf("\n\n  initialization ok, version is:  %s \n\n",ccs1[0]);

   printf("  stylefiles is  %d\n\n", stylefiles);

   printf("\n enter any character to request prologue(s)\n");

   scanf("%c",&c1);

   printf("\n\n");


/*  in what follows, assume stylefiles equal to 2  */



/*  the prologue(s)  */

   s1 = qisgnl.prologue ;

   csl[0] = qisgnl.y ;
   csl[1] = qisgnl.y ;

   qinterf2018c(&s1,&s2,(CFI_cdesc_t *)&ccsf,csl,&lintc);

   if ( s2 != qrsgnl.ok ) {
      printf("\n error_message:  %s\n\n", ccs1[0]);
      exit(1);
   }

   ij = -1 ;
   printf(".........................................................\n");
   while ( ++ij < stylefiles ) {
      printf("\n prologue %d, length of output-block is %d \n", ij+1, csl[ij]);
      printf(".........................................................\n");
      printf("%s\n", ccs1[ij]);
      printf(".........................................................\n");
   }



   printf("\n\n now enter any character to request the amplitudes\n \
   those for the first three diagrams will be displayed\n");

   scanf("%c\n",&c1);

   printf("\n\n");



/*  the output-blocks for the diagram section  */

   k1 = (int_least64_t) 0 ;
   s2 = qrsgnl.ok ;

   while ( s2 == qrsgnl.ok ) {

      s1 = qisgnl.diagram ;

      csl[0] = qisgnl.y ;
      csl[1] = qisgnl.y ;

      qinterf2018c(&s1,&s2,(CFI_cdesc_t *)&ccsf,csl,&lintc);

      if ( s2 == qrsgnl.ok ) {

         ++k1 ;
         ij = -1 ;
         while ( ++ij < stylefiles ) {
            if ( s2 != qrsgnl.end ) {
               if ( k1 < 4 ) {
                  printf(".........................................................\n");
                  printf("     diagram %d\n",k1);
                  printf("\n   output-block %d ,  length %d ,  strlen= %d \n",ij+1,csl[ij],strlen(ccs1[ij]));
                  printf(".........................................................\n");
                  printf("%s\n",ccs1[ij]);
                  printf(".........................................................\n\n");
               }
            }
         }

         if ( csl[0] > 0 ) {
            fprintf(fout1,"%s\n",ccs1[0]);
         }

         if ( csl[1] > 0 ) {
            fprintf(fout2,"%s\n",ccs1[1]);
         }

      } else {

         if ( s2 == qrsgnl.end ) {
            printf("\n #diagrams = %d\n\n",lintc);
         } else {
            printf("\n error_message:  %s\n\n", ccs1[0]);
         }
      }

      if ( k1 < 4 ) {
         printf("\n  that was diagram %d, enter another character to continue\n",k1);
         scanf("%c\n",&c1);
      }

   }



/*  getting current msg_count  */

   s1 = qisgnl.msg_count ;

   qinterf2018c(&s1,&s2,(CFI_cdesc_t *)&ccsf,csl,&lintc);

   if ( s2 != qrsgnl.ok ) {
      printf("\n error_message:  %s\n\n", ccs1[0]);
      exit(1);
   } else {
      ij = (int_least32_t) lintc;
      printf("\n  current msg_count:  %d\n", ij);
   }


/*  stopping qgraf  */


   s1 = qisgnl.stop ;

   qinterf2018c(&s1,&s2,(CFI_cdesc_t *)&ccsf,csl,&lintc);

   if ( s2 != qrsgnl.ok ) {
      printf("\n error_message:  %s\n\n", ccs1[0]);
      exit(1);
   } else {
      printf("\n  qgraf has been stopped\n\n");
   }

   fclose(fout1);
   fclose(fout2);

   exit(0);

}

