

#include <memory.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "qgraf.h"




 int main()
{

   int_least32_t  maxlen[A_SIZE], csl[A_SIZE];

   int_least32_t  s1, s2 ;

   int_least64_t  lintc, k1 ;

   int  ij, stylefiles, cfi_stat ;

   char  ccs[CCS_L0];

   char  *ccs1[A_SIZE];

   char  c1, c2 ;

/*   void  qinterf2008c ;  */


   maxlen[0] = (int_least32_t) 4096 ;
   maxlen[1] = (int_least32_t) 2048 ;


/*  some basic definitions  */

/*   slen0 = CCS_L0 ;  */

   stylefiles = 2 ;

   s1 = qisgnl.init ;

   s2 = qrsgnl.ok ;

   csl[0] = maxlen[0];
   csl[1] = maxlen[1];


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

   memcpy(ccs1[0],"'q_api.dat'\0",13);

   lintc = (int_least64_t) CCS_L0 ;

   qinterf2008c(&s1,&s2,ccs,csl,&lintc);

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


   printf("\n\n  initialization ok, version is: %s \n\n",ccs1[0]);

   printf("  stylefiles is  %d\n\n", stylefiles);

   printf("\n  enter any character to request prologue(s)\n");
   printf("\n (to enter a character means pressing the key of that character\n");
   printf("  and then pressing the return key)\n");

   scanf("%c",&c1);

   printf("\n\n");


/*  in what follows, assume stylefiles equal to 2  */



/*  the prologue(s)  */

   s1 = qisgnl.prologue ;

   csl[0] = qisgnl.y ;
   csl[1] = qisgnl.y ;

   qinterf2008c(&s1,&s2,ccs,csl,&lintc);


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

   printf("\n\n now enter any character to request the amplitudes\n");

   scanf("%c\n",&c2);

   printf("\n\n");



/*  the output-blocks for the diagram section  */


   k1 = (int_least64_t) 0 ;
   s2 = qrsgnl.ok ;

   while ( s2 == qrsgnl.ok ) {

      s1 = qisgnl.diagram ;

      csl[0] = qisgnl.y ;
      csl[1] = qisgnl.y ;

      qinterf2008c(&s1,&s2,ccs,csl,&lintc);

      if ( s2 == qrsgnl.ok ) {

         ++k1 ;
         ij = -1 ;
         while ( ++ij < stylefiles ) {
            if ( s2 != qrsgnl.end ) {
               if ( k1 < 4 ) {
                  printf(".........................................................\n");
                  printf("     diagram %d\n",k1);
                  printf("\n   output-block %d  , length %d \n",ij+1,csl[ij]);
                  printf(".........................................................\n");
                  printf("%s\n",ccs1[ij]);
                  printf(".........................................................\n\n");
               }
            }
         }

         if ( k1 < 4 ) {
            printf("\n  that was diagram %d, enter another character to continue\n",k1);
            scanf("%c\n",&c1);
         }

      } else {

         if ( s2 == qrsgnl.end ) {
            printf("\n #diagrams = %d\n\n",lintc);
         } else {
            printf("\n error_message:  %s\n\n", ccs1[0]);
         }

      }

   }


/*  getting current msg_count  */

   s1 = qisgnl.msg_count ;

   qinterf2008c(&s1,&s2,ccs,csl,&lintc);

   if ( s2 != qrsgnl.ok ) {
      printf("\n error_message:  %s\n\n", ccs1[0]);
      exit(1);
   } else {
      ij = (int_least32_t) lintc;
      printf("\n  current msg_count:  %d\n", ij);
   }


/*  stopping qgraf  */


   s1 = qisgnl.stop ;

   qinterf2008c(&s1,&s2,ccs,csl,&lintc);

   if ( s2 != qrsgnl.ok ) {
      printf("\n error_message:  %s\n\n", ccs1[0]);
      exit(1);
   } else {
      printf("\n  qgraf has been stopped\n\n");
   }


   exit(0);

}

