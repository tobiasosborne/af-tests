

  qgraf : Makefile  qgraf-4.0.6.f08
#
#	\nice \rm -f q*.mod
	\nice \rm -f fmodules/q*.mod
	\nice \gfortran -o qgraf -cpp -P -Os -J fmodules qgraf-4.0.6.f08
	\nice \chmod 750 qgraf
	\nice \rm -f fmodules/q*.mod
#	\nice \rm -f q*.mod



  pxq   : Makefile  qgraf-4.0.6.f08 api_mode/pxq.c api_mode/qgraf.h
#
#	\nice \rm -f q*.mod
	\nice \rm -f fmodules/q*.mod
	\nice \gfortran -c -o qgraf_api-4.0.6.o -cpp -P -DQ_API -DQ_F2018 -std=f2018 -ffree-form -Os -J fmodules -Wc-binding-type qgraf-4.0.6.f08
	\nice \chmod 640 qgraf_api-4.0.6.o
	\nice \gcc -o pxq -lgfortran -cpp -P -DQ_API -DQ_F2018 -Os -std=c17 qgraf_api-4.0.6.o api_mode/pxq.c
	\nice \chmod 750 pxq
	\nice \rm -f fmodules/q*.mod
#	\nice \rm -f q*.mod



  pxq08 : Makefile  qgraf-4.0.6.f08 api_mode/pxq08.c api_mode/qgraf.h
#
#	\nice \rm -f q*.mod
	\nice \rm -f fmodules/q*.mod
	\nice \gfortran -c -o qgraf_api-4.0.6.o -cpp -P -DQ_API -DQ_F2008 -std=f2008 -ffree-form -Os -J fmodules -Wc-binding-type qgraf-4.0.6.f08
	\nice \gcc -o pxq08 -cpp -P -DQ_API -DQ_F2008 -lgfortran -Os -std=c99 qgraf_api-4.0.6.o api_mode/pxq08.c
	\nice \chmod 750 pxq08
	\nice \rm -f fmodules/q*.mod
#	\nice \rm -f q*.mod



  pf08  : Makefile  api_mode/pf08.f08 qgraf-4.0.6.f08
#
#	\nice \rm -f q*.mod
	\nice \rm -f fmodules/q*.mod
	\nice \gfortran -c -o qgraf_api-4.0.6.o -cpp -P -DQ_API -std=f2008 -ffree-form -Os -J fmodules qgraf-4.0.6.f08
	\nice \gfortran -o pf08 -cpp -P -DQ_API -std=f2008 -ffree-form -Os -J fmodules -Wconversion-extra qgraf_api-4.0.6.o api_mode/pf08.f08
	\nice \chmod 750 pf08
	\nice \rm -f fmodules/q*.mod
#	\nice \rm -f q*.mod




  clean :
	\nice \rm -f fmodules/q*.mod
#	\nice \rm -f q*.mod
#	\nice \rm -f out/*
	\nice \rm -f qgraf qgraf_api-4.0.6.o pxq pxq08 pf08
	\nice \sync

