

   program pf08

      use, intrinsic :: iso_c_binding, only : c_ptr,c_char,c_int_least32_t,c_int_least64_t,c_null_char

      use, non_intrinsic :: q_api, only : ccs_l0,srec,qisgnl,qrsgnl,qinterf2008f

      implicit none
      save


!   interface block for subroutine my_error_checking (which is included in this file)
!
!      external :: my_error_checking


   interface

      subroutine my_error_checking(j1,j2,ccs,csl)

         import c_int_least32_t,c_char

         integer(kind=c_int_least32_t), intent(in) :: j1,j2

         character(kind=c_char,len=:), intent(in), allocatable :: ccs

         integer(kind=c_int_least32_t), intent(inout), allocatable :: csl(:)

      end subroutine

   end interface


!
!   max allowed line length
!
      integer, parameter :: max_length=120

!
!   in this example there are two output-blocks (and two style-files)
!

      integer(kind=c_int_least32_t), parameter :: a_size_0=2

!
!   if qout is nonzero then two output-files are created
!
      integer, parameter :: qout=1


      integer(kind=c_int_least32_t), target, allocatable :: csl(:), csl0(:)

      integer(kind=c_int_least32_t) :: clen0(1:a_size_0), ccso(1:a_size_0)

      integer(kind=c_int_least32_t) :: ccs_l, stylefiles

      integer(kind=c_int_least64_t) :: lint, max_count, k1

      integer(kind=c_int_least32_t) :: i1, j1, j2, j3, k2, ios, iunit(1:2)

      character(kind=c_char,len=:), allocatable, target :: ccs

      character(kind=c_char,len=:), pointer :: ccs_p

      character(len=1) :: c3

      logical :: loun



!   preliminary variable allocations and initializations
!
!   1. choose number of output-blocks and their maximum lengths
!       (in this example, all the declared maximum lengths are equal to 4096);
!
!       each entry of array clen0 may be comprised (independently) between 128 and 16384


      stylefiles=2

      clen0(:)=int(4096,c_int_least32_t)


!   allocate "csl0" and "csl"

      ios=1
      allocate(integer(kind=c_int_least32_t) :: csl(1:a_size_0),stat=ios)
      if( ios /= 0 )then
         print *,"  failed to allocate 'csl' "
         stop
      end if

      allocate(integer(kind=c_int_least32_t) :: csl0(1:a_size_0),stat=ios)
      if( ios /= 0 )then
         print *,"  failed to allocate 'csl0' "
         stop
      end if


!   compute offsets for output-blocks

      ccs_l=0
      do i1=1,stylefiles
         ccso(i1)=ccs_l
         ccs_l=ccs_l+clen0(i1)
      end do

      print *," "
      print *,"  (total) length of ccs equals ",ccs_l

      if( ccs_l > ccs_l0 )then
         print *," error: (total) length of ccs is too large "
         stop
      end if


!   allocate character string ccs

      ios=1
      allocate(character(kind=c_char,len=ccs_l) :: ccs,stat=ios)
      if( ios /= 0 )then
         print *,"  failed to allocate 'ccs' (1)"
         stop
      end if


      ccs_p => ccs


!   other initializations
!    (eg to make sure that the compiler does not
!     complain about non-initialized variables)

      j2=qrsgnl%ok


!   initialize qgraf  (first time)
!    write control-file name in ccs_c(*), in the first 120 positions,
!    within single-quotes, and possibly padded with white space

      j1=qisgnl%init

      ccs(1:max_length+1)="'q_api.dat'"//c_null_char

      do i1=1,stylefiles
         csl(i1)=clen0(i1)
      end do

      lint=int(len(ccs),c_int_least64_t)

      call qinterf2008f(j1,j2,ccs_p,csl,lint)


!   initialization ok if ( j2 == qrsgnl%ok )

      if( j2 /= qrsgnl%ok )then
         write(*,fmt='(/(a)/)')'  there was a problem with the initialization'
         call my_error_checking(j1,j2,ccs,csl)
      else
         write(*,fmt='(/(a)/)')'  initialization ok,  version : '//ccs(1:csl(1))
         write(*,fmt='(/(a),i0/)')'                     #style-files :  ',lint
      end if

      if( lint /= int(stylefiles,c_int_least64_t) )then
         print *,'......................................................................'
         print *,'  there was an unexpected problem with #style-files'
         print *,'......................................................................'
         print *,'  #style-files=',stylefiles,'       lint=',lint
         print *,'......................................................................'
         print *,''
         stop
      end if


      print *,''
      print *,"   enter 'y' to continue"
      print *,"   (to enter a character means pressing the key of that character"
      print *,"    and then pressing the return key)"
      read(*,*)c3
      if( ( c3 /= 'y' ) .and. ( c3 /= 'Y' ) )then
         stop
      end if

!
!   count diagrams, up to the number declared in "lint"
!    (if csl(1) is set as qisgnl%y)
!

      max_count=int(99999,c_int_least64_t)

      j1=qisgnl%count

      lint=max_count

      call qinterf2008f(j1,j2,ccs_p,csl,lint)

!   count ok if ( j2 == qrsgnl%ok )

      if( j2 /= qrsgnl%ok )then
         write(*,fmt='(/(a)/)')'  there was a problem with the diagram count'
         call my_error_checking(j1,j2,ccs,csl)
      end if

      print *,''
      print *,'......................................................................'
      print *,''
      if( ( j3 == qisgnl%n ) .or. ( lint < max_count ) )then
         print *,'  preliminary diagram_count = ',lint
      else
         print *,'  preliminary (min_)diagram_count = ',lint
      end if
      print *,''
      print *,'                  max_count = ',max_count
      print *,'......................................................................'
      print *,''


      print *,''
      print *,"   enter 'y' to continue"
      read(*,*)c3
      if( ( c3 /= 'y' ) .and. ( c3 /= 'Y' ) )then
         stop
      end if


!
!   re-initialize qgraf before prologue(s), ...
!    (let us assume that the control-file does not change,
!     so that "stylefiles" remains fixed during the whole run)
!

      j1=qisgnl%init

      ccs(1:max_length+1)="'q_api.dat'"//c_null_char

      do i1=1,stylefiles
         csl(i1)=clen0(i1)
      end do

      lint=int(len(ccs),c_int_least64_t)

      call qinterf2008f(j1,j2,ccs_p,csl,lint)


!   re-initialization ok if ( j2 == qrsgnl%ok )

      if( j2 /= qrsgnl%ok )then
         write(*,fmt='(/(a)/)')'  there was a problem with the re-initialization (2)'
         call my_error_checking(j1,j2,ccs,csl)
      else
         write(*,fmt='(/(a)/)')'  re-initialization ok (2)'
         write(*,fmt='(/(a),i0/)')'                     #style-files :  ',lint
      end if


      print *,''
      print *,"   enter 'y' to continue"
      read(*,*)c3
      if( ( c3 /= 'y' ) .and. ( c3 /= 'Y' ) )then
         stop
      end if



!
!   open two output-files (if #style-files > 1 )
!
!     this example saves the output-blocks in computer files,
!     but in general that may not be necessary
!

      if( qout /= 0 )then

         ios=1
         loun=.true.
         inquire(file='out_tmp/out.1',exist=loun,iostat=ios)

         if( loun )then
            write(*,fmt='(/(a)/)')"  file out_tmp/out.1 exists, enter 'y' to delete it"
            read(*,*)c3
            if( ( c3 == 'y' ) .or. ( c3 == 'Y' ) )then
               call execute_command_line('\rm -f out_tmp/out.1')
            else
               stop
            end if
         end if

         open(access='sequential',action='write',file='out_tmp/out.1',iostat=ios,newunit=iunit(1),status='new')

         if( ios .ne. 0 )then
            write(*,fmt='(/(a)/)')'  error: file out_tmp/out.1 (possibly created by "pf08") could not be opened'
            stop
         end if

         if( stylefiles > 1 )then

            ios=1
            loun=.true.
            inquire(file='out_tmp/out.2',exist=loun,iostat=ios)

            if( loun )then
               write(*,fmt='(/(a)/)')"  file out_tmp/out.2 exists, enter 'y' to delete it"
               read(*,*)c3
               if( ( c3 == 'y' ) .or. ( c3 == 'Y' ) )then
                  call execute_command_line('\rm -f out_tmp/out.2')
               else
                  stop
               end if
            end if

         end if

         open(access='sequential',action='write',file='out_tmp/out.2',iostat=ios,newunit=iunit(2),status='new')

         if( ios .ne. 0 )then
            write(*,fmt='(/(a)/)')'  error: file out_tmp/out.2 (possibly created by "pf08") could not be opened'
            stop
         end if

      end if


      print *,''
      print *,'  new files  out_tmp/out.1 and out_tmp/out.2  have been opened'
      print *,''
      print *,"   enter 'y' to continue"
      read(*,*)c3
      if( ( c3 /= 'y' ) .and. ( c3 /= 'Y' ) )then
         stop
      end if


!
!   the prologue(s)
!

      j1=qisgnl%prologue

      csl(1:stylefiles)=qisgnl%y

      call qinterf2008f(j1,j2,ccs_p,csl,lint)


      if( j2 /= qrsgnl%ok )then
         write(*,fmt='(/(a)/)')'  there was a problem with the prologue(s)'
         call my_error_checking(j1,j2,ccs,csl)
      end if

!   here the strings ccs() contain the "prologue(s)"

      print *,''

      do i1=1,stylefiles

         print *,'......................................................................'
         print *,'   prologue',i1,'     length=',csl(i1)
         print *,'......................................................................'
         write(*,fmt='(a)')ccs(ccso(i1)+1:ccso(i1)+csl(i1))
         print *,'......................................................................'
         print *,''

         if( ( qout /= 0 ) .and. ( csl(i1) > 0 ) )then
            write(unit=iunit(i1),fmt='(a)')ccs(ccso(i1)+1:ccso(i1)+csl(i1))
         end if

      end do

      print *,''
      print *,'   prologue(s) ok'
      print *,"   enter 'y' to continue"
      read(*,*)c3
      if( ( c3 /= 'y' ) .and. ( c3 /= 'Y' ) )then
         stop
      end if



!  getting current msg_count

      j1=qisgnl%msg_count

      call qinterf2008f(j1,j2,ccs_p,csl,lint)

      if ( j2 /= qrsgnl%ok )then
         print *,'  error_message: '//ccs(1:csl(1))
      else
         j3=int(lint)
         print *,'  current msg_count: ',lint
      end if


      print *,''
      print *,"   enter 'y' to continue"
      read(*,*)c3
      if( ( c3 /= 'y' ) .and. ( c3 /= 'Y' ) )then
         stop
      end if


!
!  the output-blocks for the diagram section
!
!   now call qgraf once per diagram
!
!   upon return, for each i = 1, ... , stylefiles,
!   the value of csl(i) is the length of output-block "i" stored in ccs
!   (excluding the terminating null character)

!   which output-blocks to request?
!    only the first, in this example

      csl0(1)=qisgnl%y
      csl0(2)=qisgnl%n


      k1=0

      do while( j2 == qrsgnl%ok )

         j1=qisgnl%diagram

         do i1=1,stylefiles
            csl(i1)=csl0(i1)
         end do

         call qinterf2008f(j1,j2,ccs_p,csl,lint)

         if( ( j2 /= qrsgnl%ok ) .and. ( j2 /= qrsgnl%end ) )then
            write(*,fmt='(/(a,i11,a,i4)/)')'  there was a problem with output-block ',(lint),'  diagram ',k1+1
            call my_error_checking(j1,j2,ccs,csl)
         end if

!
!   another possible cross-check
!
         do i1=1,stylefiles
            if( csl(i1) > clen0(i1) )then
               write(*,fmt='(/(a)/)')'  there was a problem: output-block is too long'
            end if
         end do


!   the "amplitudes" are in ccs
!    the output-blocks for the first 2 diagrams are displayed
!     (but only for style-file #1, with the above choice)


         if( j2 == qrsgnl%ok )then

            k1=k1+1

            do i1=1,stylefiles

               if( csl0(i1) == qisgnl%y )then

                  if( j2 /= qrsgnl%end )then
!                     print *,''
!                     print *,'   diagram',k1
                     if( k1 < 3 )then
                        print *,''
                        print *,'......................................................................'
                        print *,'   diagram',k1
                        print *,''
                        print *,'   output-block',i1,'     length=',csl(i1)
                        print *,'......................................................................'
                        write(*,fmt='(a)')ccs(ccso(i1)+1:ccso(i1)+csl(i1))
                        print *,'......................................................................'
                        print *,''
                     end if
                  end if

                  if( ( qout /= 0 ) .and. ( csl(i1) > 0 ) )then
                     write(unit=iunit(i1),fmt='(a)')ccs(ccso(i1)+1:ccso(i1)+csl(i1))
                  end if

               end if

            end do

            if( k1 == 2 )then
               print *,''
               print *,'   first two diagrams ok'
               print *,"   enter 'y' to continue"
               read(*,*)c3
            end if

         end if

      end do


      print *,''
      print *,'  #diagrams=',lint
      print *,''
      print *,''
      print *,'   diagram(s) ok'
      print *,"   enter 'y' to continue"
      read(*,*)c3
      if( ( c3 /= 'y' ) .and. ( c3 /= 'Y' ) )then
         stop
      end if


!
!   the epilogue(s)
!

      j1=qisgnl%epilogue
      csl(1:stylefiles)=qisgnl%y

      call qinterf2008f(j1,j2,ccs_p,csl,lint)

      if( j2 /= qrsgnl%ok )then
         write(*,fmt='(/(a)/)')'  there was a problem with the epilogue(s)'
         call my_error_checking(j1,j2,ccs,csl)
      end if

!
!   the epilogues are in ccs()
!

      do i1=1,stylefiles

         print *,'......................................................................'
         print *,'   epilogue',i1,'     length=',csl(i1)
         print *,'......................................................................'
         write(*,fmt='(a)')ccs(ccso(i1)+1:ccso(i1)+csl(i1))
         print *,'......................................................................'
         print *,''

         if( ( qout /= 0 ) .and. ( csl(i1) > 0 ) )then
            write(unit=iunit(i1),fmt='(a)')ccs(ccso(i1)+1:ccso(i1)+csl(i1))
         end if

      end do

      print *,''
      print *,'   epilogue(s) ok'
      print *,"   enter 'y' to continue"
      read(*,*)c3
      if( ( c3 /= 'y' ) .and. ( c3 /= 'Y' ) )then
         stop
      end if


!
!   stop qgraf (close or delete the message-file)
!

      j1=qisgnl%stop

      call qinterf2008f(j1,j2,ccs_p,csl,lint)


      if( j2 /= qrsgnl%ok )then
         write(*,fmt='(/(a)/)')'  there was a problem with stopping'
         call my_error_checking(j1,j2,ccs,csl)
      else
         write(*,fmt='(/(a)/)')'  qgraf stopped ok'
      end if

      print *,''
      print *,'......................................................................'
      print *,''


!
!  close the two output files opened earlier
!

      if( qout /= 0 )then
         close(unit=iunit(1))
         close(unit=iunit(2))
      end if

      write(*,fmt='(/(a)/)')'  output-files closed'


!   deallocate csl, ccs

      if( allocated(ccs) )then
!         print *,' length of css : ',len(ccs)
         deallocate(ccs,stat=ios)
!         write(*,fmt='(/(a)/)')'  ccs  deallocated'
      end if


      if( allocated(csl) )then
         deallocate(csl)
!         write(*,fmt='(/(a)/)')'  csl  deallocated'
      end if


      stop


   end program pf08








   subroutine my_error_checking(sgnl1,sgnl2,ccs,csl)

      use, non_intrinsic :: q_api, only : a_size_0,qisgnl,qrsgnl

      use, intrinsic :: iso_c_binding, only : c_char,c_int_least32_t,c_int_least32_t,c_null_char

      implicit none
      save


      integer(kind=c_int_least32_t), intent(in) :: sgnl1,sgnl2

      character(kind=c_char,len=:), intent(in), allocatable :: ccs

      integer(kind=c_int_least32_t), intent(inout), allocatable :: csl(:)

      integer, parameter :: l0=120

      integer :: k2

      intrinsic min


      if( sgnl2 /= qrsgnl%ok )then
         if( ( sgnl1 /= qisgnl%diagram ) .or. ( sgnl2 /= qrsgnl%end ) )then

            if( sgnl2 == qrsgnl%input_error )then
               write(*,fmt='(/(a)/)')'  call was not successful, error_type is "qrsgnl%input_error"  '
            elseif( sgnl2 == qrsgnl%q_error )then
               write(*,fmt='(/(a)/)')'  call was not successful, error_type is "qrsgnl%q_error"  '
            elseif( sgnl2 == qrsgnl%os_error )then
               write(*,fmt='(/(a)/)')'  call was not successful, error_type is "qrsgnl%os_error"  '
            end if

            if( allocated(ccs) )then
               if( allocated(csl) )then

                  k2=min(int(csl(1)),l0)

                  print *,''
                  print *,'   csl(1)= ',csl(1)
                  print *,'......................................................................'
                  write(*,fmt='(a)')'  msg:  '//ccs(1:k2)
                  print *,'......................................................................'
                  print *,''

               end if
            end if

            stop

         end if
      end if


   end subroutine my_error_checking



