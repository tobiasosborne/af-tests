!
! -------------------------------------------------------------
!
!     qgraf-4.0.6
!     a module for Feynman diagram generation
!
!     copyright 1990--2026 by Paulo Nogueira (Universidade de Lisboa)
!
!     not to be redistributed without explicit permission
!
!
!     documentation:
!
!       [1] file 'qgraf-4.0.6.pdf'
!
!     related literature:
!
!       [2] Automatic Feynman graph generation
!           J. Comput. Phys. 105 (1993) 279--289
!           https://doi.org/10.1006/jcph.1993.1074
!
!       [3] Abusing Qgraf
!           Nucl. Instrum. Methods Phys. Res. A 559 (2006) 220--223
!           https://doi.org/10.1016/j.nima.2005.11.151
!
!       [4] Feynman graph generation and propagator mixing, I
!           Comput. Phys. Commun. 269 (2021) 108103
!           https://doi.org/10.1016/j.cpc.2021.108103
!
! -------------------------------------------------------------
!
!     Disclaimer and License:
!
!     This program is copyrighted but may be used for Academic
!     Research and Teaching purposes in basic scientific fields,
!     specially Physics. It may be downloaded, compiled, and
!     then executed in a computer; if necessary, the source
!     file may be edited to modify a few internal parameters,
!     in accordance with the instructions provided in the
!     respective documentation.
!     Any other use is unauthorized including, but not limited
!     to, use in commercial and mission-critical environments.
!
!     As it should be clear -- not least because this is a
!     not-for-profit research tool -- there is no warranty of
!     any kind, including suitability for any purpose.
!
!     With two exceptions, detailed below, redistribution is
!     also unauthorized (the term "redistribution" applies to
!     any distribution not made by the author). A version of
!     this program is _available_ if it can be obtained from
!     the program's "official website" (which is maintained
!     either by the author, or on behalf of the author); a
!     version is _stable_ if it has been declared as such, by
!     its author, in that website.
!
!     Redistributing a version ("A") of this program, as part
!     of a larger package ("P"), is authorized when all of the
!     following conditions are met. To begin with, there are
!     three preliminary conditions:
!     (1) "A" is (i.e. has been, or was) a "stable" version,
!        which is no longer available;
!     (2) "A" is necessary to the functioning of another gratis
!        non-commercial program ("B") used in Physics Research;
!     (3a) the author(s) and maintainer(s) of "B" are no longer
!        able to update "B" so that an available, "stable"
!        version of this program may be used instead, OR
!     (3b) there is no available "stable" version of this
!        program owing to the closure of the official website.
!     In that case, programs "A" and "B" (as well as any other
!     necessary programs) may be distributed gratis in a single
!     package "P", provided that
!     (4) the licenses of all those programs included in "P"
!        allow such a distribution;
!     (5) the license of "P" states that the copy of "A" thus
!        obtained cannot be used for any purpose other than
!        contributing to the functioning of "P", and refer to
!        this license;
!     (6) "A" is distributed in source form only (currently
!        Fortran), encrypted or not;
!     (7) whenever possible, the intention of distributing "P"
!        is communicated by e-mail to the author of "A".
!
!     By making their programs dependent on this program, the
!     authors of said programs agree to make reasonable efforts
!     to move the dependence from older versions of this
!     program to an available "stable" version.
!
!     Users of this program agree to communicate to its author,
!     in a timely manner, any error that they may happen to
!     find.
!
! -------------------------------------------------------------
!
#ifdef Q_API
#define Q_ERRT \
if(qerrt(0).gt.qerrty%ale)then ; \
go to 99 ; \
end if
#else
#define Q_ERRT !
#endif
module qbasic
use,intrinsic::iso_fortran_env,only:iostat_end,error_unit,output_unit
use,intrinsic::iso_c_binding,only:c_ptr,c_int_least32_t,c_int_least64_t,c_char,c_null_char,c_new_line,&
c_f_pointer
#ifndef Q_API
use,intrinsic::iso_c_binding,only:c_char,c_null_char
#endif
implicit none
save
integer,parameter::asciik=selected_char_kind('ASCII')
integer(kind=c_int_least32_t),parameter::anull=0
integer(kind=c_int_least32_t),parameter::atab=9
integer(kind=c_int_least32_t),parameter::alf=10
integer(kind=c_int_least32_t),parameter::srec=121
integer(kind=c_int_least32_t),parameter::srecx=127
integer(kind=c_int_least32_t),parameter::qerrl0=240
character(kind=asciik,len=srec)::blak
character(kind=asciik,len=srecx)::coarg
character(kind=asciik,len=qerrl0)::qerrmsg,dmsg
type qerrtyp
integer(kind=c_int_least32_t)::qend,ok,ale,inp,q,os,ubo
end type qerrtyp
type(qerrtyp),parameter::qerrty=qerrtyp(&
qend=-1,&
ok=0,&
ale=1,&
inp=2,&
q=3,&
os=4,&
ubo=4)
integer(kind=c_int_least32_t)::qerrt(0:2),serrt
integer(kind=c_int_least32_t)::qerrmsgl
integer(kind=c_int_least32_t)::ios=0
integer(kind=c_int_least32_t)::mas=0
integer(kind=c_int_least32_t),parameter::srec0=81
integer(kind=c_int_least32_t),parameter::srec00=101
integer(kind=c_int_least32_t),parameter::sdrec=72
end module qbasic
module qbounds
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::scbuff0=1048575
integer(kind=c_int_least32_t),parameter::sibuff0=8388607
integer(kind=c_int_least32_t),parameter::swbuff0=32767
integer(kind=c_int_least32_t),parameter::sxbuff0=2047
integer(kind=c_int_least32_t),parameter::intubo0=46340
integer(kind=c_int_least32_t),parameter::sfiles0=7
#ifdef Q_API
integer(kind=c_int_least32_t),parameter::a_size_0=int(sfiles0,c_int_least32_t)
integer(kind=c_int_least32_t),parameter::ccs_l0=int(46080,c_int_least32_t)
#endif
integer(kind=c_int_least32_t),parameter::nafiles0=4
integer(kind=c_int_least32_t),parameter::sjbuff0=16383
integer(kind=c_int_least32_t),parameter::maxphi0=intubo0
integer(kind=c_int_least32_t),parameter::maxvertx0=intubo0
integer(kind=c_int_least32_t),parameter::maxleg=11
integer(kind=c_int_least32_t),parameter::maxrho=7
integer(kind=c_int_least32_t),parameter::maxdeg=8
integer(kind=c_int_least32_t),parameter::maxn=2*max(maxleg-1,maxrho-1)
integer(kind=c_int_least32_t),parameter::maxli=maxn+maxrho
integer(kind=c_int_least32_t),parameter::qb1=(maxleg*(maxleg-1))/2
integer(kind=c_int_least32_t),parameter::qb2=2*maxn+2*maxrho+maxdeg
integer(kind=c_int_least32_t),parameter::ihdexp=15
type zboty
integer(kind=c_int_least32_t)::iref,irefl,wiref,wirefl,wirefh,spten
integer(kind=c_int_least32_t)::iref10,irefl10
integer(kind=c_int_least64_t)::irefh,irefh10
end type zboty
type(zboty)::zbo
integer(kind=c_int_least32_t)::slhp(0:0),slhl(0:0)
type zinty
integer(kind=c_int_least32_t)::s,l,h
end type zinty
type(zinty),parameter::inty=zinty(&
s=1,&
l=2,&
h=3)
end module qbounds
module qaski
use,non_intrinsic::qbasic
implicit none
save
integer,parameter::aspc=iachar(' ')
integer,parameter::adq=iachar('"')
integer,parameter::asq=iachar("'")
integer,parameter::acomma=iachar(',')
integer,parameter::acol=iachar(':')
integer,parameter::ascol=iachar(';')
integer,parameter::adot=iachar('.')
integer,parameter::alsbr=iachar('[')
integer,parameter::arsbr=iachar(']')
integer,parameter::alcbr=iachar('{')
integer,parameter::arcbr=iachar('}')
integer,parameter::alpar=iachar('(')
integer,parameter::arpar=iachar(')')
integer,parameter::aminus=iachar('-')
integer,parameter::aplus=iachar('+')
integer,parameter::aast=iachar('*')
integer,parameter::aslash=iachar('/')
integer,parameter::aeq=iachar('=')
integer,parameter::agt=iachar('>')
integer,parameter::alt=iachar('<')
integer,parameter::abslash=iachar('\')
integer,parameter::ausc=iachar('_')
integer,parameter::acirc=iachar('^')
integer,parameter::avbar=iachar('|')
integer,parameter::anine=iachar('9')
integer,parameter::azero=iachar('0')
integer,parameter::ahash=iachar('#')
integer,parameter::apcent=iachar('%')
integer(kind=c_int_least32_t)::abo(0:6),acf(0:255),punct1(0:0)
integer(kind=c_int_least32_t),parameter::ncrs0=4
integer(kind=c_int_least32_t)::crs(1:ncrs0,1:6)
type chtyp
integer(kind=c_int_least32_t)::nond,annot,usco,digit,ucase,lcase
end type chtyp
type(chtyp),parameter::chty=chtyp(&
nond=-2,&
annot=-1,&
usco=0,&
digit=1,&
ucase=2,&
lcase=3)
type strtyp
integer(kind=c_int_least32_t)::p,id,sqs,z,dqs,q,ns,minus,plus,ast
end type strtyp
type(strtyp),parameter::strty=strtyp(&
p=1,&
id=2,&
sqs=3,&
z=4,&
dqs=5,&
q=6,&
ns=7,&
minus=8,&
plus=9,&
ast=10)
integer(kind=c_int_least32_t),parameter::dcol=257
integer(kind=c_int_least32_t),parameter::dscol=258
integer(kind=c_int_least32_t),parameter::dslash=259
integer(kind=c_int_least32_t),parameter::dsq=260
end module qaski
module qcbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::stcbdst0=6
character(kind=asciik,len=:),target,allocatable::xstcb,ystcb
character(kind=asciik,len=:),pointer::stcb
integer(kind=c_int_least32_t)::stcbas(1:1),stcbdst(1:1),stcbs(1:1),stmbs(1:1)
integer(kind=c_int_least32_t)::scbff(0:stcbdst0)
integer(kind=c_int_least32_t)::dcff0
end module qcbuffer
module qzbuffer
use,non_intrinsic::qbounds,only:sjbuff0
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::stibdst0=9
integer(kind=c_int_least32_t),parameter::stj0=4
integer(kind=c_int_least32_t),target,allocatable::xstib(:),ystib(:)
integer(kind=c_int_least32_t),pointer::stib(:)
integer(kind=c_int_least32_t)::diff0
integer(kind=c_int_least32_t)::stibas(1:1),stibdst(1:1),stibs(1:1)
integer(kind=c_int_least32_t)::sibff(0:stibdst0)
integer(kind=c_int_least32_t)::stjb(1:sjbuff0+1)
integer(kind=c_int_least32_t)::jbco(0:128)
integer(kind=c_int_least32_t)::stjbs
integer(kind=c_int_least32_t)::nstjb
end module qzbuffer
module qkeys
use,non_intrinsic::qbasic
implicit none
save
type argtyp
integer(kind=c_int_least32_t)::vers,help,xtch,file,hash,pcent,amk,bom,nobom,ubo
integer(kind=c_int_least32_t)::mc34,mc44,mc43,mc42,sc34,sc43,sc42,bc34,bc43,subm,submn
end type argtyp
type(argtyp),parameter::argty=argtyp(&
vers=1,&
help=2,&
xtch=3,&
file=4,&
amk=5,&
hash=6,&
pcent=7,&
subm=8,&
submn=9,&
mc34=10,&
mc44=11,&
mc43=12,&
mc42=13,&
sc34=14,&
sc43=15,&
sc42=16,&
bc34=17,&
bc43=18,&
bom=19,&
nobom=20,&
ubo=21)
type proctyp
integer(kind=c_int_least32_t)::inf,ninf,ins,nins,unk
end type proctyp
type(proctyp),parameter::procty=proctyp(&
inf=1,&
ninf=2,&
ins=3,&
nins=4,&
unk=5)
type dekcty
integer(kind=c_int_least32_t)::conf,psep,odir,sdir,mdir,ldir,msg,outp,sty,lib,&
model,in,out,loop,opt,part,off,maxc,zerok,loopk,tru,fal,ubo
end type dekcty
type(dekcty),parameter::dekc=dekcty(&
conf=1,&
psep=2,&
odir=3,&
sdir=4,&
mdir=5,&
ldir=6,&
msg=7,&
sty=8,&
outp=9,&
lib=10,&
model=11,&
in=12,&
out=13,&
loop=14,&
loopk=15,&
opt=16,&
part=17,&
off=18,&
maxc=19,&
zerok=20,&
tru=21,&
fal=22,&
ubo=22)
integer(kind=c_int_least32_t)::comc(1:dekc%ubo)
type qmode
integer(kind=c_int_least32_t)::api,auto,fcon
end type qmode
type(qmode),parameter::qmod=qmode(&
api=1,&
auto=2,&
fcon=3)
integer(kind=c_int_least32_t)::qxmod
type dsplmode
integer(kind=c_int_least32_t)::dflt,noinfo,info,dbg,vrbs
end type dsplmode
type(dsplmode),parameter::dsplmod=dsplmode(&
dflt=0,&
noinfo=1,&
info=2,&
dbg=3,&
vrbs=4)
type cfopt
integer(kind=c_int_least32_t)::qlist,del,flsh,lf,noblank,nontnls,nontlf,xchar,noopt,psep
integer(kind=c_int_least32_t)::maxc,dioff,subm,pq,hidpq,loopk,msg,part,qn,bom,dspl,ubo
end type cfopt
type(cfopt),parameter::confi=cfopt(&
qlist=1,&
del=2,&
flsh=3,&
lf=4,&
noblank=5,&
nontnls=6,&
nontlf=7,&
xchar=8,&
noopt=9,&
psep=10,&
maxc=11,&
dioff=12,&
subm=13,&
pq=14,&
hidpq=15,&
loopk=16,&
msg=17,&
part=18,&
qn=19,&
bom=20,&
dspl=21,&
ubo=21)
type mflagtyp
integer(kind=c_int_least32_t)::one,cac,even,diff,ext,notadp,vdup,fpath
integer(kind=c_int_least32_t)::tskt,npskt,pninskt,tpskt,nvskt,vninskt,tvskt,nsubm,ubo
end type mflagtyp
type(mflagtyp),parameter::mflaty=mflagtyp(&
one=1,&
cac=2,&
even=3,&
diff=4,&
ext=5,&
notadp=6,&
vdup=7,&
fpath=8,&
pninskt=9,&
npskt=10,&
tpskt=11,&
vninskt=12,&
nvskt=13,&
tvskt=14,&
tskt=15,&
nsubm=16,&
ubo=16)
type opektyp
integer(kind=c_int_least32_t)::bnb,link,sum
end type opektyp
type(opektyp),parameter::opekty=opektyp(&
bnb=1,&
sum=2,&
link=3)
type opetyp
integer(kind=c_int_least32_t)::iprop,bridge,sbridge,rbridge,chord,vsum,psum,elink,plink
end type opetyp
type(opetyp),parameter::opety=opetyp(&
iprop=1,&
bridge=2,&
sbridge=3,&
rbridge=4,&
chord=5,&
vsum=6,&
psum=7,&
elink=11,&
plink=12)
type dekmty
integer(kind=c_int_least32_t)::sbm_stm,sk_stm
integer(kind=c_int_least32_t)::c_stm,c_gdef,c_gdft,sbmb_c
integer(kind=c_int_least32_t)::f_stm,f_gdft,f_sdft
integer(kind=c_int_least32_t)::sbmb_stm,sbmb_sk,sbmb_end
integer(kind=c_int_least32_t)::skb_stm,skb_end
integer(kind=c_int_least32_t)::p_def
integer(kind=c_int_least32_t)::v_def
integer(kind=c_int_least32_t)::ubo
end type dekmty
type(dekmty),parameter::dekm=dekmty(&
sbm_stm=1,&
sk_stm=2,&
c_stm=3,&
c_gdef=4,&
c_gdft=5,&
f_stm=6,&
f_gdft=7,&
sbmb_stm=8,&
sbmb_sk=9,&
sbmb_c=10,&
sbmb_end=11,&
skb_stm=12,&
f_sdft=13,&
p_def=14,&
v_def=15,&
skb_end=16,&
ubo=16)
type mlltyp
integer(kind=c_int_least32_t)::mc,mff,mpf,mvf,msm,msk
end type mlltyp
type(mlltyp),parameter::mllty=mlltyp(&
mc=1,&
mff=2,&
mpf=3,&
mvf=4,&
msm=5,&
msk=6)
type stmtyp
integer(kind=c_int_least32_t)::uopt,ureq,dopt,dreq
end type stmtyp
type(stmtyp),parameter::stmty=stmtyp(&
uopt=0,&
dopt=1,&
ureq=2,&
dreq=3)
integer(kind=c_int_least32_t)::pisk(0:0),wisk(0:0),cisk(0:0),fisk(0:0)
integer(kind=c_int_least32_t)::oisk(0:0),aisk(0:0)
integer(kind=c_int_least32_t)::poptcl(0:0),woptcl(0:0),coptcl(0:0),aoptcl(0:0)
integer(kind=c_int_least32_t)::popt0(0:0),wopt0(0:0),copt0(0:0),aopt0(0:0),xopt0(0:0)
integer(kind=c_int_least32_t)::popt1(0:0),wopt1(0:0),copt1(0:0),aopt1(0:0),xopt1(0:0)
integer(kind=c_int_least32_t)::popt2(0:0),wopt2(0:0),copt2(0:0),aopt2(0:0),xopt2(0:0)
integer(kind=c_int_least32_t)::popt3(0:0),wopt3(0:0),copt3(0:0),aopt3(0:0)
integer(kind=c_int_least32_t)::popt4(0:0),wopt4(0:0),copt4(0:0),aopt4(0:0)
integer(kind=c_int_least32_t)::popt5(0:0),wopt5(0:0),copt5(0:0),aopt5(0:0),xopt5(0:0)
integer(kind=c_int_least32_t)::popt6(0:0),wopt6(0:0),copt6(0:0),aopt6(0:0)
integer(kind=c_int_least32_t)::popt7(0:0),wopt7(0:0),copt7(0:0),aopt7(0:0)
integer(kind=c_int_least32_t)::popt9(0:0),wopt9(0:0),copt9(0:0),aopt9(0:0)
integer(kind=c_int_least32_t)::kc(0:0),kse(0:0),pske(0:0),wske(0:0),aske(0:0)
integer(kind=c_int_least32_t)::nske,mcopt2,ncopt2
integer(kind=c_int_least32_t)::xgfnp(0:0),xgfnl(0:0),xstypp(0:0),xstypl(0:0)
integer(kind=c_int_least32_t)::xtstrp(0:0),xtstrl(0:0),mprep(0:0),mprel(0:0)
type elintyp
integer(kind=c_int_least32_t)::incl,excl
end type elintyp
type(elintyp),parameter::elinty=elintyp(&
incl=0,&
excl=1)
type dflagtyp
integer(kind=c_int_least32_t)::nob,norb,nosb,edge,onsh,onshx,onshxe,nosig,nosn,cyc
integer(kind=c_int_least32_t)::ovi,bip,nosl,nodl,nopa,simp,idx,newe,newc,newp,newt,newa
integer(kind=c_int_least32_t)::fl,vsum,psum,esym,elink,plink,topo,ubo
end type dflagtyp
type(dflagtyp),parameter::dflaty=dflagtyp(&
nob=1,&
norb=2,&
nosb=3,&
edge=4,&
onsh=5,&
onshx=6,&
onshxe=7,&
nosig=8,&
nosn=9,&
cyc=10,&
ovi=11,&
bip=12,&
nosl=13,&
nodl=14,&
nopa=15,&
simp=16,&
idx=17,&
newe=18,&
newt=19,&
newp=20,&
newc=21,&
newa=22,&
fl=23,&
vsum=24,&
psum=25,&
esym=26,&
elink=27,&
plink=28,&
topo=29,&
ubo=29)
type jflagtyp
integer(kind=c_int_least32_t)::noga,noge,nogc,nogp,pari,sclf,scstg,scppar,init,ingg,vexc,pexc
integer(kind=c_int_least32_t)::backmod,nconst,mflang,nw,nwf,noaut,intlp,intlzp,zmom,smom,ubo
end type jflagtyp
type(jflagtyp),parameter::jflaty=jflagtyp(&
noga=1,&
noge=2,&
nogc=3,&
nogp=4,&
pari=5,&
sclf=6,&
scstg=7,&
scppar=8,&
init=9,&
ingg=10,&
vexc=11,&
pexc=12,&
backmod=13,&
nconst=14,&
mflang=15,&
nw=16,&
nwf=17,&
noaut=18,&
intlp=19,&
intlzp=20,&
zmom=21,&
smom=22,&
ubo=22)
type edgetyp
integer(kind=c_int_least32_t)::re,se,rb,sb,rnb,snb
end type edgetyp
type(edgetyp),parameter::edgty=edgetyp(&
re=1,&
se=2,&
rb=1,&
sb=2,&
rnb=-1,&
snb=-2)
end module qkeys
module qintr
use,non_intrinsic::qbounds,only:sibuff0
use,non_intrinsic::qkeys
use,non_intrinsic::qbasic
implicit none
save
type qcontrol
integer(kind=c_int_least32_t)::c,p,t,e,d,ubo
end type qcontrol
type(qcontrol),parameter::qcntr=qcontrol(&
d=1,&
e=2,&
t=3,&
p=4,&
c=5,&
ubo=5)
integer(kind=c_int_least32_t)::outd(1:qcntr%ubo),qco(1:qcntr%ubo),qcntrx,qsgnl
type qmatcs
integer(kind=c_int_least32_t)::lc,oc,ls,os
end type qmatcs
type(qmatcs),parameter::qmatc=qmatcs(&
lc=-1,&
oc=-2,&
ls=9,&
os=8)
integer(kind=c_int_least32_t),parameter::nap=-((sibuff0-1)/3)
integer(kind=c_int_least32_t),parameter::eoa=(nap+1)/3
integer(kind=c_int_least32_t),parameter::eosf=eoa/3
integer(kind=c_int_least32_t)::cflag(1:confi%ubo)=0
integer(kind=c_int_least32_t)::dflag(1:dflaty%ubo)=0
integer(kind=c_int_least32_t)::jflag(1:jflaty%ubo)=0
integer(kind=c_int_least32_t),parameter::mll0=6
type qqll
integer(kind=c_int_least32_t)::kl,dcs,n
integer(kind=c_int_least32_t)::p1,p2
end type qqll
type(qqll),target::qll(1:mll0)=qqll(kl=0,dcs=0,n=0,p1=0,p2=0)
type qqllkla
integer(kind=c_int_least32_t)::klss,klcf
end type qqllkla
type(qqllkla)::qllkla=qqllkla(&
klss=1,&
klcf=2)
integer(kind=c_int_least32_t)::qvl=0
integer(kind=c_int_least32_t)::dprefl=0
integer(kind=c_int_least32_t)::qvp,dprefp
integer(kind=c_int_least32_t)::qtfpp,qtfpq,qgfmp,qgfmq
integer(kind=c_int_least32_t),parameter::ptenp(0:0)=[0]
integer(kind=c_int_least32_t)::aaf(0:4)
type udirs
integer(kind=c_int_least32_t)::ldirp,ldirq
integer(kind=c_int_least32_t)::mdirp,mdirq
integer(kind=c_int_least32_t)::odirp,odirq
integer(kind=c_int_least32_t)::sdirp,sdirq
integer(kind=c_int_least32_t)::ubo
end type udirs
type(udirs),parameter::udir=udirs(&
sdirp=1,&
sdirq=2,&
mdirp=3,&
mdirq=4,&
odirp=5,&
odirq=6,&
ldirp=7,&
ldirq=8,&
ubo=8)
end module qintr
module qwbuffer
use,non_intrinsic::qbounds
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::swbuff1=swbuff0+(swbuff0+1)/2
integer(kind=c_int_least32_t)::stwbpf(1:sfiles0),stwbqf(1:sfiles0),stwbuf(1:sfiles0)
character(kind=c_char,len=:),target,allocatable::xstwb
character(kind=c_char,len=:),pointer::stwb
character(kind=asciik,len=sxbuff0+1)::stxb
character(kind=asciik,len=sxbuff0+1),allocatable::stmb
character(kind=asciik,len=sdrec)::sthb1,sthb2
character(kind=asciik,len=ihdexp+1)::zstr
end module qwbuffer
module qfiles
use,non_intrinsic::qintr,only:udir
use,non_intrinsic::qbounds,only:sfiles0,nafiles0
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::non_unit=-1
integer::p_sep
type qftyp
integer(kind=c_int_least32_t)::ctyp,wtyp,mtyp,ltyp,styp,gityp,otyp,ptyp
integer(kind=c_int_least32_t)::gotyp,mdirtyp,sdirtyp,odirtyp,ubo
end type qftyp
type(qftyp),parameter::qfty=qftyp(&
ctyp=1,&
wtyp=2,&
ltyp=3,&
mtyp=4,&
styp=5,&
gityp=6,&
gotyp=7,&
otyp=8,&
ptyp=9,&
mdirtyp=10,&
odirtyp=11,&
sdirtyp=12,&
ubo=12)
integer(kind=c_int_least32_t)::csyfty(1:qfty%ubo)
type qfdtyp
integer(kind=c_int_least32_t)::dno,dok
end type qfdtyp
type(qfdtyp),parameter::qfdty=qfdtyp(&
dno=0,&
dok=1)
type rectyp
integer(kind=c_int_least32_t)::len,tail,annot,err,fchar,xchar,ubo
end type rectyp
type(rectyp),parameter::recty=rectyp(&
len=1,&
tail=2,&
annot=3,&
err=4,&
fchar=5,&
xchar=6,&
ubo=6)
integer(kind=c_int_least32_t)::recdty(1:recty%ubo)
integer(kind=c_int_least32_t),parameter::mfiles0=2*sfiles0+nafiles0
integer(kind=c_int_least32_t)::filp(1:mfiles0),filq(1:mfiles0),filu(1:mfiles0)
integer(kind=c_int_least32_t)::film(1:mfiles0),filo(1:mfiles0),filt(1:mfiles0),fild(1:mfiles0)
integer(kind=c_int_least32_t)::fila(1:mfiles0),filb(1:mfiles0),filc(1:mfiles0),filw(1:mfiles0)
integer(kind=c_int_least32_t)::nfiles,nsfiles,dso
integer,parameter::ubom(1:3)=[239,187,191]
integer(kind=c_int_least32_t),parameter::stapi0=4
integer(kind=c_int_least32_t)::stapi(1:stapi0),stapj(0:0)
integer(kind=c_int_least32_t)::stapis
integer(kind=c_int_least32_t)::irecc(0:0),frecc(0:0)
integer(kind=c_int_least32_t)::ndrec,ncom,rlink
integer(kind=c_int_least32_t),parameter::smat0=88
character(kind=asciik,len=smat0)::smat
integer(kind=c_int_least32_t)::udirpq(1:udir%ubo)
integer(kind=c_int_least32_t)::f1x
type qobso
integer(kind=c_int_least32_t)::cf,mf,sf,topol,simple,ubo
end type qobso
type(qobso),parameter::qobs=qobso(&
cf=1,&
mf=2,&
sf=3,&
topol=4,&
simple=5,&
ubo=6)
integer(kind=c_int_least32_t)::qobsol(1:recty%ubo)
end module qfiles
module qfcon
use,non_intrinsic::qbounds
use,non_intrinsic::qfiles,only:non_unit
use,non_intrinsic::qkeys
use,non_intrinsic::qbasic
type fctyp
integer(kind=c_int_least32_t)::mc,sc,bc
end type fctyp
type(fctyp),parameter::fcty=fctyp(&
mc=1,&
sc=2,&
bc=3)
integer(kind=c_int_least32_t),parameter::njpq=11
integer(kind=c_int_least32_t)::nskec,pskec(0:0),wskec(0:0),askec(0:0),jp(1:njpq),jq(1:njpq)
integer(kind=c_int_least32_t)::sekts1(0:0),sekts2(0:0)
integer(kind=c_int_least32_t)::nlin34a,nlin34b
integer(kind=c_int_least32_t)::tofc,stofc
integer(kind=c_int_least32_t)::iamk
integer(kind=c_int_least32_t)::tfu=non_unit
integer(kind=c_int_least32_t)::stsb(1:sjbuff0+1)
integer(kind=c_int_least32_t),parameter::sts0=4
integer(kind=c_int_least32_t)::nstsb=0
integer(kind=c_int_least32_t)::stsbs
integer(kind=c_int_least32_t)::fcsc(1:dekm%ubo)=0
integer(kind=c_int_least32_t),parameter::blines0=2
end module qfcon
module qmix
use,non_intrinsic::qbounds,only:maxn,maxdeg,maxli,maxrho,maxleg
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::n,nli
type qnsym
integer(kind=c_int_least32_t)::es,i,l,nl,ubo
end type qnsym
type(qnsym),parameter::symt=qnsym(&
i=0,&
nl=1,&
l=2,&
es=3,&
ubo=3)
integer(kind=c_int_least32_t)::dis,ngsym,psyms,psym(0:0),ndsym(0:symt%ubo)
type qdcotyp
integer(kind=c_int_least32_t)::maxc,offix,off,nat,part,loop,ubo
end type qdcotyp
type(qdcotyp),parameter::dcoty=qdcotyp(&
maxc=-1,&
offix=0,&
off=1,&
nat=2,&
part=3,&
loop=4,&
ubo=4)
integer(kind=c_int_least32_t)::qcop(-1:dcoty%ubo),qcol(-1:dcoty%ubo)
integer(kind=c_int_least32_t)::mrho,nrho,rhop1,rhop2
integer(kind=c_int_least32_t)::rho(-1:maxdeg),xn(1:maxn),gam(1:maxn,1:maxn)
integer(kind=c_int_least32_t)::vdeg(1:maxn),vxl(1:maxn),vfo(1:maxn)
integer(kind=c_int_least32_t)::lmap(1:maxn,1:maxdeg),vmap(1:maxn,1:maxdeg)
integer(kind=c_int_least32_t)::pmap(1:maxn,1:maxdeg),vlis(1:maxn),invlis(1:maxn)
integer(kind=c_int_least32_t)::rdeg(1:maxn),sdeg(1:maxn),amap(1:maxn,1:maxdeg)
integer(kind=c_int_least32_t)::ex0(1:maxli),ey0(1:maxli),ex(1:maxli),ey(1:maxli)
integer(kind=c_int_least32_t)::ovm(1:maxn,1:maxdeg),iovm(1:maxn,1:maxdeg)
integer(kind=c_int_least32_t)::ntadp,net(-3:3),xtail(1:maxn),xhead(1:maxn)
integer(kind=c_int_least32_t)::flow(1:maxli,0:maxleg+maxrho),ege(1:maxn,1:maxn)
integer(kind=c_int_least32_t)::oflow(0:maxli,1:maxleg)
integer(kind=c_int_least32_t)::zpro(0:maxli),zcho(0:maxli),zbri(0:maxli)
integer(kind=c_int_least32_t)::rbri(0:maxli),sbri(0:maxli)
integer(kind=c_int_least32_t)::vdpi(0:0),vdpj(0:0)
integer(kind=c_int_least32_t)::efinvdc(0:0),efm(0:0)
end module qmix
module qimodel
use,non_intrinsic::qintr,only:nap
use,non_intrinsic::qkeys,only:mflaty
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::smodp(0:0),smodq(0:0)
integer(kind=c_int_least32_t)::mflag(1:mflaty%ubo)=0
type phityp
integer(kind=c_int_least32_t)::dflt,notdp,int,ntint,ext
end type phityp
type(phityp),parameter::phity=phityp(&
dflt=0,&
notdp=1,&
int=2,&
ntint=3,&
ext=5)
type futype
integer(kind=c_int_least32_t)::sqs,dqs,id,q,z
end type futype
type(futype),parameter::futyp=futype(&
sqs=1,&
dqs=2,&
id=3,&
q=4,&
z=5)
integer(kind=c_int_least32_t)::nphi,nprop,npprop,nvert
integer(kind=c_int_least32_t)::nblok,nblokfp,blok(0:0)
integer(kind=c_int_least32_t)::nudk,ngmk,npmk,nvmk
integer(kind=c_int_least32_t)::namep(0:0),namel(0:0),link(0:0),antiq(0:0)
integer(kind=c_int_least32_t)::nivd(0:0),dpntro(0:0),vparto(0:0),vval(0:0)
integer(kind=c_int_least32_t)::nivdx(0:0)
integer(kind=c_int_least32_t)::gmkp(0:0),gmkl(0:0),gmkr(0:0),gmko(0:0)
integer(kind=c_int_least32_t)::gmkvp(0:0),gmkvl(0:0),gmkvt(0:0)
integer(kind=c_int_least32_t)::pmkp(0:0),pmkl(0:0),pmkd(0:0),pmkt(0:0)
integer(kind=c_int_least32_t)::pmkvma(0:0),pmkvmi(0:0),pmkzp(0:0),psfi(0:0)
integer(kind=c_int_least32_t)::pmkvfpp(0:0),pmkvflp(0:0)
integer(kind=c_int_least32_t)::vmkp(0:0),vmkl(0:0),vmkt(0:0),vmks(0:0)
integer(kind=c_int_least32_t)::vmkmao(0:0),vmkmio(0:0),vmkzp(0:0),vsfi(0:0)
integer(kind=c_int_least32_t)::vmkvpp(0:0),vmkvlp(0:0)
end module qimodel
#ifdef Q_API
module q_api
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
type qisgnls
integer(kind=c_int_least32_t)::pre_init,init,msg_count,count,stop,prologue,diagram,epilogue
integer(kind=c_int_least32_t)::hold,elinks,topology,partition,loops,y,n
integer(kind=c_int_least32_t)::lbo,ubo
end type qisgnls
type(qisgnls),parameter::qisgnl=qisgnls(&
pre_init=int(-8,c_int_least32_t),&
init=int(-9,c_int_least32_t),&
msg_count=int(-10,c_int_least32_t),&
count=int(-11,c_int_least32_t),&
stop=int(-12,c_int_least32_t),&
prologue=int(-13,c_int_least32_t),&
diagram=int(-14,c_int_least32_t),&
epilogue=int(-15,c_int_least32_t),&
hold=int(-16,c_int_least32_t),&
elinks=int(-17,c_int_least32_t),&
topology=int(-18,c_int_least32_t),&
partition=int(-19,c_int_least32_t),&
loops=int(-20,c_int_least32_t),&
y=int(-21,c_int_least32_t),&
n=int(-22,c_int_least32_t),&
lbo=-22,&
ubo=-8)
integer(kind=c_int_least32_t),parameter::qisgnl_ob(qisgnl%lbo:qisgnl%ubo)=[0,0,1,1,1,1,1,1,1,1,0,0,0,0,0]
integer(kind=c_int_least32_t),parameter::qisgnl_d(qisgnl%lbo:qisgnl%ubo)=[0,0,1,1,1,1,1,0,1,0,0,0,0,0,0]
type qrsgnls
integer(kind=c_int_least32_t)::ok,end,input_error,q_error,os_error
end type qrsgnls
type(qrsgnls),parameter::qrsgnl=qrsgnls(&
ok=int(-2-qerrty%ok,c_int_least32_t),&
end=int(-4-qerrty%qend,c_int_least32_t),&
input_error=int(-2-qerrty%inp,c_int_least32_t),&
q_error=int(-2-qerrty%q,c_int_least32_t),&
os_error=int(-2-qerrty%os,c_int_least32_t))
integer(kind=c_int_least32_t),parameter::ccs_l1=128
integer(kind=c_int_least32_t),parameter::ccs_l2=16384
integer(kind=c_int_least32_t),parameter::ccs_l3=8
integer(kind=c_int_least32_t),pointer::oblen(:)
integer(kind=c_int_least32_t)::obsel(1:a_size_0)
integer(kind=c_int_least32_t)::moblen(1:a_size_0)
integer(kind=c_int_least32_t)::qpsgnl=qisgnl%pre_init
contains
subroutine qpout(junit)
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qkeys
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::junit
integer(kind=c_int_least32_t)::f1,i1,j1,j2,j3
f1=filo(junit)
j1=stwbpf(f1)+1
j2=stwbqf(f1)
serrt=qerrty%ok
if(j1.le.0)then
serrt=qerrty%q
else if(j2.lt.j1-1)then
serrt=qerrty%q
else if(filt(junit).ne.qfty%ptyp)then
serrt=qerrty%q
else if(oblen(f1).ne.int(0,c_int_least32_t))then
serrt=qerrty%q
else if((j2-j1).gt.moblen(f1))then
serrt=qerrty%inp
end if
if(j2.ge.j1)then
if(iachar(stwb(j2:j2)).ne.alf)then
serrt=qerrty%q
end if
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qpout_1'//c_null_char
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
if(cflag(confi%nontlf).eq.0)then
do while(j2.ge.j1)
if(iachar(stwb(j2:j2)).eq.alf)then
j2=j2-1
else
exit
end if
end do
else
j3=j1-1
do i1=j1,j2
if(iachar(stwb(i1:i1)).ne.alf)then
j3=j3+1
stwb(j3:j3)=stwb(i1:i1)
end if
end do
j2=j3
end if
if(j2.ge.j1)then
j2=j2+1
stwb(j2:j2)=c_null_char
oblen(f1)=int(j2-j1,c_int_least32_t)
else
stwb(j1:j1)=c_null_char
oblen(f1)=int(0,c_int_least32_t)
end if
99 continue
return
end subroutine qpout
subroutine qinterf2008f(sgnl1,sgnl2,ccs,csl,lint)
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::sgnl1
integer(kind=c_int_least32_t),intent(out)::sgnl2
character(kind=c_char,len=:),pointer,intent(inout)::ccs
integer(kind=c_int_least32_t),target,intent(inout)::csl(1:a_size_0)
integer(kind=c_int_least64_t),intent(inout)::lint
call qfportal(sgnl1,sgnl2,ccs,csl,lint)
99 continue
return
end subroutine qinterf2008f
#ifdef Q_F2008
subroutine qinterf2008c(sgnl1,sgnl2,ccs_c,csl,lint) bind(C,name="qinterf2008c")
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::sgnl1
integer(kind=c_int_least32_t),intent(out)::sgnl2
type(c_ptr),value::ccs_c
integer(kind=c_int_least32_t),target,intent(inout)::csl(1:a_size_0)
integer(kind=c_int_least64_t),intent(inout)::lint
character(kind=c_char,len=:),pointer::ccs_f
ccs_f=>null()
call c_f_pointer(ccs_c,ccs_f)
call qfportal(sgnl1,sgnl2,ccs_f,csl,lint)
99 continue
return
end subroutine qinterf2008c
#endif
#ifdef Q_F2018
subroutine qinterf2018c(sgnl1,sgnl2,ccs_c,csl,lint) bind(C,name="qinterf2018c")
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::sgnl1
integer(kind=c_int_least32_t),intent(out)::sgnl2
character(kind=c_char,len=*),intent(inout),target::ccs_c
integer(kind=c_int_least32_t),target,intent(inout)::csl(1:a_size_0)
integer(kind=c_int_least64_t),intent(inout)::lint
character(kind=c_char,len=:),pointer::ccs_f
ccs_f=>ccs_c
call qfportal(sgnl1,sgnl2,ccs_f,csl,lint)
99 continue
return
end subroutine qinterf2018c
#endif
subroutine qfportal(sgnl1,sgnl2,ccs,csl,lint)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel,only:mflag
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::sgnl1
integer(kind=c_int_least32_t),intent(out)::sgnl2
character(kind=c_char,len=:),pointer::ccs
integer(kind=c_int_least32_t),target,intent(inout)::csl(1:a_size_0)
integer(kind=c_int_least64_t),intent(inout)::lint
integer(kind=c_int_least32_t), external::qstdz
integer(kind=c_int_least32_t)::ccs_tl,intsgnl1
integer(kind=c_int_least32_t)::stav(qisgnl%lbo:qisgnl%ubo)
integer(kind=c_int_least32_t)::i1,j1,j2,j3,j4,k1,k2,nzcsel,alok
if(qpsgnl.eq.qisgnl%pre_init)then
cflag(:)=0
dflag(:)=0
jflag(:)=0
mflag(:)=0
qxmod=qmod%api
cflag(confi%dspl)=dsplmod%noinfo
if(sgnl1.ne.qisgnl%init)then
serrt=qerrty%inp
call qpomsg(8)
Q_ERRT
end if
end if
sgnl2=qrsgnl%ok
f1x=0
if(qerrt(0).gt.qerrty%ale)then
if((qerrt(0).ne.qerrty%inp).or.&
(sgnl1.ne.qisgnl%init))then
call qpomsg(8)
Q_ERRT
end if
end if
qerrt(0)=qerrty%ok
if(sgnl1.ne.qisgnl%init)then
if(sgnl1.ne.qisgnl%count)then
lint=int(0,c_int_least64_t)
end if
end if
serrt=qerrty%ok
if(sgnl1.lt.int(qisgnl%lbo,c_int_least32_t))then
serrt=qerrty%inp
else if(sgnl1.ge.int(qisgnl%ubo,c_int_least32_t))then
serrt=qerrty%inp
else if(sgnl1.ne.qisgnl%init)then
if((qpsgnl.eq.qisgnl%stop).or.&
(qpsgnl.eq.qisgnl%pre_init))then
serrt=qerrty%inp
end if
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qpomsg(10)
Q_ERRT
end if
alok=1
stwb=>ccs
if(.not.associated(stwb))then
alok=0
qerrt(0)=qerrty%inp
call qpomsg(1)
Q_ERRT
end if
oblen=>csl
if(.not.associated(oblen))then
alok=0
qerrt(0)=qerrty%inp
call qpomsg(2)
Q_ERRT
end if
if(sgnl1.ne.qisgnl%init)then
if(size(oblen).lt.max(1,nsfiles))then
qerrt(0)=qerrty%inp
call qpomsg(4)
Q_ERRT
end if
end if
if(sgnl1.eq.qisgnl%init)then
stav(:)=0
call qclose(0)
Q_ERRT
coarg(1:srecx)=stwb(1:srecx)
call qinputs
Q_ERRT
end if
nzcsel=0
if(nsfiles.eq.0)then
if(qisgnl_ob(sgnl1).ne.0)then
qerrt(0)=qerrty%inp
call qpomsg(9)
Q_ERRT
end if
else if(nsfiles.gt.0)then
if(size(oblen).lt.max(1,nsfiles))then
qerrt(0)=qerrty%inp
call qpomsg(4)
Q_ERRT
end if
if(sgnl1.eq.qisgnl%init)then
ccs_tl=0
do i1=1,nsfiles
if((oblen(i1).lt.ccs_l1).or.&
(oblen(i1).gt.ccs_l2))then
qerrt(0)=qerrty%inp
call qpomsg(6)
Q_ERRT
end if
moblen(i1)=int(oblen(i1)-ccs_l3)
stwbpf(i1)=ccs_tl
stwbuf(i1)=ccs_tl+moblen(i1)+1
ccs_tl=ccs_tl+int(oblen(i1))
end do
if(int(ccs_l0,c_int_least64_t).lt.lint)then
qerrt(0)=qerrty%inp
call qpomsg(7)
Q_ERRT
end if
if(lint.lt.int(ccs_tl,c_int_least64_t))then
qerrt(0)=qerrty%inp
call qpomsg(7)
Q_ERRT
end if
else if(qisgnl_ob(sgnl1).ne.0)then
do i1=1,nsfiles
if(oblen(i1).ne.qisgnl%n)then
if(oblen(i1).eq.qisgnl%y)then
nzcsel=nzcsel+1
else
qerrt(0)=qerrty%inp
call qpomsg(2)
Q_ERRT
end if
end if
obsel(i1)=oblen(i1)
oblen(i1)=int(0,c_int_least32_t)
end do
end if
end if
if(qisgnl_d(int(sgnl1)).ne.0)then
if(sgnl1.ne.qisgnl%diagram)then
if(qpsgnl.ne.qisgnl%diagram)then
qerrt(0)=qerrty%inp
call qpomsg(8)
Q_ERRT
end if
if(sgnl1.ne.qisgnl%hold)then
if(dflag(dflaty%newa).ne.0)then
qerrt(0)=qerrty%inp
call qcfmsg(32,0,0)
Q_ERRT
end if
end if
end if
end if
intsgnl1=int(sgnl1)
select case(intsgnl1)
case(int(qisgnl%init))
stwb(1:qvl+1)=stcb(qvp:(qvp-1)+qvl)//c_null_char
oblen(1:nsfiles)=int(0,c_int_least32_t)
oblen(1)=int(qvl,c_int_least32_t)
lint=int(nsfiles,c_int_least64_t)
go to 99
case(int(qisgnl%count))
if((stav(int(sgnl1)).ne.0).or.&
(stav(int(qisgnl%count)).ne.0).or.&
(stav(int(qisgnl%diagram)).ne.0).or.&
(stav(int(qisgnl%epilogue)).ne.0))then
qerrt(0)=qerrty%inp
call qpomsg(8)
Q_ERRT
end if
if(lint.lt.int(0,c_int_least64_t))then
qerrt(0)=qerrty%inp
call qpomsg(7)
Q_ERRT
else if(lint.eq.int(0,c_int_least64_t))then
cflag(confi%maxc)=0
else
write(coarg,fmt='(i0,a)')lint,achar(aspc)
do i1=1,len(coarg)
if(iachar(coarg(i1:i1)).eq.aspc)then
j2=i1-1
exit
end if
end do
j2=qstdz(coarg,1,j2,inty%h)
Q_ERRT
qcol(dcoty%maxc)=j2
stcb(qcop(dcoty%maxc)+1:qcop(dcoty%maxc)+j2)=coarg(1:j2)
cflag(confi%maxc)=1
end if
cflag(confi%qlist)=0
lint=int(0,c_int_least64_t)
qsgnl=1
do while(qsgnl.ne.0)
call qgen
Q_ERRT
end do
if(qerrt(0).eq.qerrty%qend)then
qerrt(0)=qerrty%ok
end if
oblen(1:nsfiles)=int(0,c_int_least32_t)
read(stcb(qcop(dcoty%nat)+1:qcop(dcoty%nat)+qcol(dcoty%nat)),fmt=*)lint
stav(int(qisgnl%prologue))=-1
stav(int(qisgnl%diagram))=-1
stav(int(qisgnl%epilogue))=-1
case(int(qisgnl%diagram))
stav(int(qisgnl%prologue))=-1
if((nsfiles.eq.0).or.&
(stav(int(sgnl1)).lt.0).or.&
(stav(int(qisgnl%count)).ne.0).or.&
(stav(int(qisgnl%epilogue)).ne.0))then
qerrt(0)=qerrty%inp
call qpomsg(8)
Q_ERRT
end if
if(stav(int(qisgnl%diagram)).eq.0)then
qsgnl=1
cflag(confi%maxc)=0
cflag(confi%qlist)=1
else
if(qpsgnl.ne.sgnl1)then
qerrt(0)=qerrty%inp
call qpomsg(8)
Q_ERRT
end if
end if
call qgen
Q_ERRT
go to 99
case(int(qisgnl%hold))
if(qpsgnl.eq.qisgnl%diagram)then
cflag(confi%qlist)=1
call qompac
Q_ERRT
else
qerrt(0)=qerrty%inp
call qpomsg(8)
Q_ERRT
end if
go to 99
case(int(qisgnl%prologue))
if((nsfiles.eq.0).or.&
(stav(int(sgnl1)).ne.0).or.&
(stav(int(qisgnl%count)).ne.0).or.&
(stav(int(qisgnl%diagram)).ne.0).or.&
(stav(int(qisgnl%epilogue)).ne.0))then
qerrt(0)=qerrty%inp
call qpomsg(8)
Q_ERRT
else if(stav(int(sgnl1)).ne.0)then
qerrt(0)=qerrty%qend
else
cflag(confi%qlist)=1
jflag(jflaty%ingg)=0
call qpropos
Q_ERRT
end if
go to 99
case(int(qisgnl%epilogue))
stav(int(qisgnl%prologue))=-1
stav(int(qisgnl%diagram))=-1
if((nsfiles.eq.0).or.&
((stav(int(qisgnl%count)).eq.0).and.(stav(int(qisgnl%diagram)).eq.0)).or.&
(stav(int(sgnl1)).ne.0))then
qerrt(0)=qerrty%inp
call qpomsg(8)
Q_ERRT
else if(stav(int(sgnl1)).gt.0)then
stav(int(sgnl1))=-1
qerrt(0)=qerrty%qend
else
cflag(confi%qlist)=1
jflag(jflaty%ingg)=-1
call qpropos
Q_ERRT
end if
go to 99
case(int(qisgnl%stop))
call qclose(0)
Q_ERRT
lint=int(jflag(jflaty%nw),c_int_least64_t)
qpsgnl=qisgnl%pre_init
go to 99
case(int(qisgnl%msg_count))
lint=int(jflag(jflaty%nw),c_int_least64_t)
case(int(qisgnl%elinks))
dflag(dflaty%newe)=1
call qgen
Q_ERRT
dflag(dflaty%newe)=0
go to 99
case(int(qisgnl%topology))
dflag(dflaty%newt)=1
call qgen
Q_ERRT
dflag(dflaty%newt)=0
go to 99
case(int(qisgnl%partition))
dflag(dflaty%newp)=1
call qgen
Q_ERRT
dflag(dflaty%newp)=0
go to 99
case(int(qisgnl%loops))
dflag(dflaty%newc)=1
call qgen
Q_ERRT
dflag(dflaty%newc)=0
go to 99
case default
qerrt(0)=qerrty%inp
call qpomsg(10)
Q_ERRT
end select
99 continue
if(alok.ne.0)then
if(.not.associated(stwb))then
stwb=>ccs
end if
if(.not.associated(oblen))then
oblen=>csl
end if
end if
if(qerrt(0).gt.qerrty%ale)then
if(associated(stwb))then
j2=srec-1
do i1=1,j2
if(iachar(qerrmsg(i1:i1)).eq.anull)then
j2=i1-1
exit
end if
end do
if(j2.gt.0)then
stwb(1:j2)=qerrmsg(1:j2)
end if
j2=j2+1
stwb(j2:j2)=c_null_char
do i1=j2+1,srec
stwb(i1:i1)=achar(aspc)
end do
j2=j2-1
if(associated(oblen))then
oblen(1:nsfiles)=int(0,c_int_least32_t)
oblen(1)=int(j2,c_int_least32_t)
end if
end if
stav(int(sgnl1))=-1
else
if(stav(int(sgnl1)).eq.0)then
stav(int(sgnl1))=1
end if
if(qisgnl_d(int(sgnl1)).ne.0)then
if(qsgnl.ne.1)then
sgnl2=qrsgnl%end
stav(int(qisgnl%diagram))=-1
if(associated(oblen))then
oblen(1:nsfiles)=int(0,c_int_least32_t)
end if
read(stcb(qcop(dcoty%nat)+1:qcop(dcoty%nat)+qcol(dcoty%nat)),fmt=*)lint
else
stav(int(qisgnl%diagram))=1
end if
end if
end if
if(qisgnl_d(int(sgnl1)).eq.0)then
qpsgnl=sgnl1
sgnl2=int(-2-qerrt(0),c_int_least32_t)
else
qpsgnl=qisgnl%diagram
if(sgnl2.ne.qrsgnl%end)then
sgnl2=int(-2-qerrt(0),c_int_least32_t)
end if
end if
if(f1x.gt.0)then
lint=int(f1x,c_int_least64_t)
f1x=0
end if
stwb=>null()
oblen=>null()
if(qerrt(0).eq.qerrty%ale)then
qerrt(0)=qerrty%ok
end if
return
end subroutine qfportal
subroutine qpomsg(jj)
use,non_intrinsic::qaski
use,non_intrinsic::qfiles
use,non_intrinsic::qkeys
use,non_intrinsic::qcbuffer
use,non_intrinsic::qzbuffer
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj
integer(kind=c_int_least32_t)::i1,j1,j2,j3,j4
select case(jj)
case(1)
qerrmsg(1:srec)="argument ccs() is not properly defined"//c_null_char
case(2)
qerrmsg(1:srec)="argument csl() is not properly defined"//c_null_char
case(3)
qerrmsg(1:srec)="argument ccs() is too small"//c_null_char
if(f1x.gt.0)then
j1=0
do i1=1,sdrec
if(qerrmsg(i1:i1).eq.c_null_char)then
j1=i1
exit
end if
end do
write(zstr,fmt='(i0,a)')f1x,achar(aminus)
j2=0
do i1=1,len(zstr)
if(iachar(zstr(i1:i1)).eq.aminus)then
j2=i1-1
exit
end if
end do
if(j2.eq.0)then
j2=1
zstr(1:1)=achar(aspc)
end if
j3=stib(xgfnp(0)+qfty%ptyp)
j4=stib(xgfnl(0)+qfty%ptyp)
qerrmsg(j1:j1+j4+j2+3)=', '//stcb(j3:(j3-1)+j4)//' '//zstr(1:j2)//c_null_char
end if
case(4)
qerrmsg(1:srec)="array csl() is too small"//c_null_char
case(5)
qerrmsg(1:srec)="input string ccs() is not valid"//c_null_char
case(6)
qerrmsg(1:srec)="input array csl() is not valid"//c_null_char
case(7)
qerrmsg(1:srec)="input 'lint' is not valid"//c_null_char
case(8)
qerrmsg(1:srec)="unexpected interface call"//c_null_char
case(9)
qerrmsg(1:srec)="error condition detected; exiting"//c_null_char
case(10)
qerrmsg(1:srec)="input argument 'sgnl1' is not valid"//c_null_char
case default
qerrt(0)=qerrty%q
qerrmsg(1:srec)="qpomsg_1"//c_null_char
end select
qerrt(0)=qerrty%inp
call qmput(0,0,0)
Q_ERRT
99 continue
return
end subroutine qpomsg
end module q_api
#endif
module qproc
use,non_intrinsic::qbounds,only:maxleg,qb1
use,non_intrinsic::qbasic,only:c_int_least32_t
implicit none
save
integer(kind=c_int_least32_t)::nleg,nloop,loopx(1:4),inco,outg,leg(0:0),deltasub
integer(kind=c_int_least32_t)::momep(0:0),momeq(0:0),momel(0:0)
integer(kind=c_int_least32_t)::momzp(0:0),momzq(0:0),momzl(0:0)
integer(kind=c_int_least32_t),parameter::kpqs(2:4)=[112,113,115]
integer(kind=c_int_least32_t)::ps1(1:maxleg),invps1(1:maxleg)
integer(kind=c_int_least32_t)::ns1,p1l(1:qb1),p1r(1:qb1)
integer(kind=c_int_least32_t)::ntf,tpc(0:0),tftyp(0:0),tfnarg(0:0)
integer(kind=c_int_least32_t)::tfa(0:0),tfb(0:0),tfc(0:0),tfo(0:0),tf2(0:0)
integer(kind=c_int_least32_t)::tfta(0:0),tftb(0:0),tftic(0:0)
integer(kind=c_int_least32_t)::tfills(0:0),tfiuls(0:0)
end module qproc
module qsty
use,non_intrinsic::qintr,only:eoa,eosf
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::maxtak=3
integer(kind=c_int_least32_t),parameter::maxpot=7
integer(kind=c_int_least32_t),parameter::skep0=105
integer(kind=c_int_least32_t)::iogp(1:4)
integer(kind=c_int_least32_t)::ks,tak(1:maxtak),pot(0:maxpot),skep(1:skep0)
integer(kind=c_int_least32_t)::udkp(0:2),udkl(0:0),udkt(0:0),udki(0:0)
integer(kind=c_int_least32_t)::kla(0:0),klo(0:0),sef(0:0)
type stylos
integer(kind=c_int_least32_t)::sto,sti,i,o,p,v,r,m,end
end type stylos
type(stylos),parameter::stylo=stylos(&
sto=-2,&
sti=-1,&
i=1,&
o=2,&
p=3,&
v=4,&
r=5,&
m=6,&
end=-3)
end module qsty
subroutine qende
use,non_intrinsic::qcbuffer,only:stcb,xstcb,ystcb
use,non_intrinsic::qintr
use,non_intrinsic::qproc,only:nloop
use,non_intrinsic::qwbuffer,only:xstwb
use,non_intrinsic::qzbuffer,only:stib,xstib,ystib
use,non_intrinsic::qbasic
implicit none
save
jflag(jflaty%ingg)=-1
if(cflag(confi%qlist).gt.0)then
cflag(confi%nontlf)=0
call qpropos
Q_ERRT
end if
call qsp(8,0,0)
Q_ERRT
call qclose(0)
Q_ERRT
stib=>null()
stcb=>null()
if(allocated(xstib))then
deallocate(xstib,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
if(allocated(ystib))then
deallocate(ystib,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
if(allocated(xstcb))then
deallocate(xstcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
if(allocated(ystcb))then
deallocate(ystcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
if(allocated(xstwb))then
deallocate(xstwb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
nloop=-1
call qstop
Q_ERRT
99 continue
return
end subroutine qende
subroutine qstop
use,non_intrinsic::qintr
use,non_intrinsic::qbasic
implicit none
save
if(qxmod.ne.qmod%api)then
stop
end if
99 continue
return
end subroutine qstop
subroutine qhelp
use,non_intrinsic::qcbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::leftab=1
integer(kind=c_int_least32_t)::j1,j2,n0
n0=0
dmsg(1:1)=char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0052790082857800497182657012006500826983696582677200847979760070798200;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
call qspak('7169786982658473787100838977667976736700826980826983697884658473797883;',n0,0,0,0)
Q_ERRT
dmsg=stcb(j1:j2-1)//stcb(j2+1:stcbs(1)-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0079700038698978776578006873657182657783120084726900707976767987737871;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
call qspak('00848980690079700067797777657868;',n0,0,0,0)
Q_ERRT
dmsg=stcb(j1:j2-1)//stcb(j2+1:stcbs(1)-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
dmsg(1:1)=char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('00000000008171826570005967797884827976137073766961;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
dmsg=stcb(j1:j2-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
dmsg(1:1)=char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0083727985766800666900698869678584696827006500707376697865776900738300;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
call qspak('787987008583856576768900826981857382696800658300658271857769788414;',n0,0,0,0)
Q_ERRT
dmsg=stcb(j1:j2-1)//stcb(j2+1:stcbs(1)-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0052790079668465737800797876890084726900656784856576000878657769006578;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
call qspak('6809008669828373797800797000847269006988696785846566766912006879;',n0,0,0,0)
Q_ERRT
dmsg=stcb(j1:j2-1)//stcb(j2+1:stcbs(1)-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
dmsg(1:1)=char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0000000000817182657000131386698283737978;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
dmsg=stcb(j1:j2-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
dmsg(1:1)=char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0038798200847269007085767600687967857769788465847379781571857368691576;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
call qspak('736769788369156873836776657377698200698467120080766965836900836969;',n0,0,0,0)
Q_ERRT
dmsg=stcb(j1:j2-1)//stcb(j2+1:stcbs(1)-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0070737669008171826570132014161422148068700065786800847269007378707982;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
call qspak('77658473797800808279867368696800797800847269008769668373846914;',n0,0,0,0)
Q_ERRT
dmsg=stcb(j1:j2-1)//stcb(j2+1:stcbs(1)-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0052727383008082797182657700738300677980898273717284696812006578680067;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
call qspak('79776983008773847200464700553350503346525700797000657889007573786814;',n0,0,0,0)
Q_ERRT
dmsg=stcb(j1:j2-1)//stcb(j2+1:stcbs(1)-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
dmsg(1:1)=char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
j1=stcbs(1)+1
call qspak('0055696683738469260072848480261515676970697765137184148469677873677914;',n0,0,0,0)
Q_ERRT
j2=stcbs(1)
call qspak('85767383667965148084159480658576791581718265701472847776;',n0,0,0,0)
Q_ERRT
dmsg=stcb(j1:j2-1)//stcb(j2+1:stcbs(1)-1)//char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
dmsg(1:1)=char(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
99 continue
return
end subroutine qhelp
subroutine qg05
use,non_intrinsic::qintr
use,non_intrinsic::qmix,only:dcoty
use,non_intrinsic::qproc,only:nloop,loopx
use,non_intrinsic::qbasic
implicit none
save
outd(qcntr%c)=0
qco(qcntr%c)=0
if(qcntrx.eq.qcntr%c)then
qcntrx=qcntr%d
end if
10 continue
if(nloop.ge.0)then
if(jflag(jflaty%noga).eq.0)then
call qsp(7,0,0)
Q_ERRT
end if
end if
if(jflag(jflaty%noga).gt.0)then
nloop=loopx(2)
call qsp(5,0,0)
Q_ERRT
else if(nloop.lt.0)then
nloop=loopx(1)
call qsp(5,0,0)
Q_ERRT
qco(qcntr%c)=1
else
if(nloop.ne.loopx(2))then
if(loopx(1).lt.loopx(2))then
nloop=nloop+1
else
nloop=nloop-1
end if
call qsp(5,0,0)
Q_ERRT
qco(qcntr%c)=1
end if
end if
if(qco(qcntr%c).ne.0)then
call qsdiag(dcoty%loop,-1)
Q_ERRT
call qrflag
Q_ERRT
if(jflag(jflaty%nogc).gt.0)then
qco(qcntr%c)=0
call qsp(6,0,0)
Q_ERRT
go to 10
end if
end if
99 continue
return
end subroutine qg05
subroutine qpg11
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::atyp,styp,nili
integer(kind=c_int_least32_t)::ii,i1,i2,i3,j1,j2,jj,kk
qco(qcntr%p)=0
if(cflag(confi%maxc).lt.0)then
go to 43
end if
if(nloop.ge.0)then
qcntrx=qcntr%d
go to 40
end if
20 continue
outd(qcntr%p)=0
if(jflag(jflaty%noga).eq.0)then
call qg05
Q_ERRT
if(qco(qcntr%c).eq.0)then
go to 70
end if
jflag(jflaty%pari)=0
else
go to 70
end if
go to 10
40 continue
jflag(jflaty%pari)=jflag(jflaty%pari)+1
43 continue
if((outd(qcntr%p).ne.0).or.&
(cflag(confi%maxc).lt.0).or.&
(jflag(jflaty%nogp).ne.0).or.&
(dflag(dflaty%newc).eq.0))then
call qsp(6,0,0)
Q_ERRT
if(cflag(confi%maxc).lt.0)then
if(qxmod.eq.qmod%auto)then
call qsp(7,0,0)
Q_ERRT
call qende
Q_ERRT
else
go to 99
end if
end if
end if
call qsdiag(dcoty%part,-1)
Q_ERRT
if(jflag(jflaty%noga).ne.0)then
go to 70
end if
if(dflag(dflaty%newc).ne.0)then
if(outd(qcntr%c).ne.0)then
go to 20
end if
end if
10 continue
j1=max(mrho,3)
kk=-1
do while (kk.ne.0)
jj=nleg+2*(nloop-1)
if((kk.lt.0).and.&
(jflag(jflaty%pari).eq.0))then
rho(:)=0
rho(-1)=nleg
rhop1=nleg+1
j2=nrho
else
ii=0
j2=j1
do i1=j1+1,nrho
if(rho(i1).gt.0)then
rho(i1)=rho(i1)-1
ii=i1
exit
else if(stib(nivd(0)+i1).gt.0)then
j2=i1
end if
end do
if(ii.eq.0)then
if(jflag(jflaty%pari).eq.0)then
if(kk.ne.0)then
rho(j1:nrho)=0
end if
go to 40
else
if(qcntrx.lt.qcntr%c)then
qcntrx=qcntr%c
end if
go to 20
end if
else
do i1=ii,nrho
jj=jj-(i1-2)*rho(i1)
end do
end if
end if
kk=jj
do i1=j2,j1,-1
if(stib(nivd(0)+i1).gt.0)then
rho(i1)=kk/(i1-2)
kk=kk-(i1-2)*rho(i1)
end if
end do
end do
jflag(jflaty%nogp)=0
if(cflag(confi%part).ne.0)then
do i1=mrho,nrho
j1=stib(vdpi(0)+i1)
j2=stib(vdpj(0)+i1)
if(j1.ge.0)then
if(j2.eq.0)then
if(rho(i1).ne.j1)then
jflag(jflaty%nogp)=-1
exit
end if
else if(j2.gt.0)then
if(rho(i1).lt.j1)then
jflag(jflaty%nogp)=-1
exit
end if
else
if(rho(i1).gt.j1)then
jflag(jflaty%nogp)=-1
exit
end if
end if
end if
end do
if(jflag(jflaty%nogp).lt.0)then
go to 40
end if
end if
if(nrho.gt.mrho)then
if(mflag(mflaty%one).eq.0)then
do i1=1,rho(-1)
if(stib(efinvdc(0)+i1).gt.0)then
j1=stib(link(0)+stib(leg(0)+i1))
j2=0
do i2=mrho,nrho
j2=j2+rho(i2)*stib(stib(efinvdc(0)+i1)+i2)
end do
if(j2.lt.stib(efm(0)+i1))then
jflag(jflaty%nogp)=1
go to 40
end if
end if
end do
end if
end if
nili=-rho(-1)
do i1=mrho,nrho
nili=nili+i1*rho(i1)
end do
nili=nili/2
if(npprop.eq.0)then
if(nili.gt.0)then
go to 40
end if
end if
if(nloop.eq.0)then
if((dflag(dflaty%nob).gt.0).or.&
(dflag(dflaty%norb).gt.0))then
if(nili.ne.0)then
go to 40
end if
else if((dflag(dflaty%nob).lt.0).or.&
(dflag(dflaty%norb).lt.0))then
if(nili.eq.0)then
go to 40
end if
end if
end if
if(zpro(nili).le.0)then
go to 40
end if
if(nloop.eq.0)then
if((zcho(0).gt.0).and.&
(zbri(nili).gt.0))then
go to 50
end if
else
do i1=nloop,nili
if(zcho(i1).gt.0)then
j1=nili-i1
if(zbri(j1).gt.0)then
do i2=0,j1
if(rbri(i2).gt.0)then
if(sbri(j1-i2).gt.0)then
go to 50
end if
end if
end do
end if
end if
end do
end if
go to 40
50 continue
if(dflag(dflaty%vsum).ne.0)then
atyp=opety%vsum
ii=stib(tftic(0)+atyp)
do i1=stib(tfta(0)+ii),stib(tftb(0)+ii)
i2=stib(tf2(0)+i1)
styp=stib(tftyp(0)+i2)
j1=0
j2=0
jj=stib(stib(tfo(0)+i2)+1)
if(stib(vmks(0)+jj).eq.0)then
qerrmsg(1:srec)='qpg11_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
do i3=nrho,mrho,-1
if(rho(i3).gt.0)then
j1=j1+rho(i3)*stib(stib(vmkmio(0)+jj)+i3)
j2=j2+rho(i3)*stib(stib(vmkmao(0)+jj)+i3)
end if
end do
if(styp.gt.0)then
if(j1.gt.stib(tfb(0)+i2))then
go to 40
else if(j2.lt.stib(tfa(0)+i2))then
go to 40
end if
else
if(j1.ge.stib(tfa(0)+i2))then
if(j2.le.stib(tfb(0)+i2))then
go to 40
end if
end if
end if
end do
end if
qco(qcntr%p)=1
jflag(jflaty%nogp)=0
70 continue
call qsdiag(dcoty%part,-1)
Q_ERRT
99 continue
return
end subroutine qpg11
subroutine qctxb(ii,jj,kk)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj,kk
integer(kind=c_int_least32_t),intent(inout)::ii
serrt=qerrty%ok
if(ii.lt.0)then
serrt=qerrty%q
else if(kk.lt.0)then
serrt=qerrty%q
else if(jj.le.0)then
serrt=qerrty%q
else if(jj.gt.(stcbas(1)-kk))then
serrt=qerrty%q
else if(jj.gt.(len(stxb)-kk))then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qctxb_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
if(jj.gt.(sxbuff0-ii))then
qerrt(0)=qerrty%q
call quput(8)
Q_ERRT
end if
stxb(ii+1:ii+jj)=stcb(kk+1:kk+jj)
ii=ii+jj
99 continue
return
end subroutine qctxb
subroutine qcbxb(ii,jj)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(inout)::ii
integer(kind=c_int_least32_t),intent(in)::jj
serrt=qerrty%ok
if(ii.lt.0)then
serrt=qerrty%q
else if(jj.le.0)then
serrt=qerrty%q
else if(jj.gt.len(blak))then
serrt=qerrty%q
else if(jj.gt.(len(stxb)-ii))then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qcbxb_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
if(jj.gt.(sxbuff0-ii))then
qerrt(0)=qerrty%q
call quput(8)
Q_ERRT
end if
stxb(ii+1:ii+jj)=blak(1:jj)
ii=ii+jj
99 continue
return
end subroutine qcbxb
subroutine qctxbz(ii,jj)
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj
integer(kind=c_int_least32_t),intent(inout)::ii
serrt=qerrty%ok
if(ii.lt.0)then
serrt=qerrty%q
else if(jj.le.0)then
serrt=qerrty%q
else if(jj.gt.len(zstr))then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qctxbz_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
if(ii.gt.(sxbuff0-jj))then
qerrt(0)=qerrty%q
call quput(8)
Q_ERRT
end if
stxb(ii+1:ii+jj)=zstr(1:jj)
ii=ii+jj
99 continue
return
end subroutine qctxbz
subroutine qsp(wot,ja,jb)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::wot,ja,jb
integer(kind=c_int_least32_t), external::qwztos
integer(kind=c_int_least32_t)::i1,i2,i3,i5,i6,j1,j2,j3,j4,j5,ii,jj,kk
integer(kind=c_int_least32_t)::subt=0
integer(kind=c_int_least32_t),parameter::leftab=2
integer(kind=c_int_least32_t)::ggx,nps(0:4),lrtab(1:5)
ii=0
if(cflag(confi%dspl).eq.dsplmod%noinfo)then
ii=1
else if(qxmod.eq.qmod%api)then
ii=1
end if
if(ii.ne.0)then
go to 99
end if
select case(wot)
case(0)
if(jflag(jflaty%scstg).ne.0)then
go to 99
end if
go to 01
case(1)
go to 11
case(2)
go to 21
case(3)
if(cflag(confi%dspl).lt.dsplmod%dbg)then
go to 99
end if
go to 31
case(4)
go to 41
case(5)
if(jflag(jflaty%scstg).lt.5)then
go to 41
else
go to 51
end if
case(6)
go to 61
case(7)
go to 71
case(8)
go to 81
case default
qerrmsg(1:srec)='qsp_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end select
01 continue
qerrt(1)=qerrt(0)
qerrt(0)=qerrty%ok
if(sdrec+1.lt.len(dmsg))then
dmsg(1:sdrec+2)=achar(alf)//sthb1(1:sdrec)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
end if
if(qvl.gt.0)then
kk=max(1,(sdrec-(qvl-1))/2)
if(kk+qvl.lt.len(dmsg))then
dmsg=blak(1:kk)//stcb(qvp:(qvp-1)+qvl)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
end if
end if
if(sdrec+1.lt.len(dmsg))then
dmsg(1:sdrec+2)=sthb1(1:sdrec)//achar(alf)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
end if
qerrt(0)=qerrt(1)
qerrt(1)=qerrty%ok
subt=0
lrtab(:)=0
jflag(jflaty%scstg)=1
go to 99
11 continue
j1=ja
do i1=ja,jb
if(iachar(stcb(i1:i1)).eq.alf)then
if(j1.lt.i1)then
dmsg=achar(aspc)//stcb(j1:i1-1)//achar(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
end if
j1=i1+1
end if
end do
jflag(jflaty%scstg)=2
go to 99
21 continue
dmsg(1:sdrec+3)=achar(alf)//sthb1(1:sdrec)//achar(alf)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
jflag(jflaty%scstg)=3
go to 99
31 continue
if(mflag(mflaty%nsubm).gt.0)then
ii=0
call qcbxb(ii,2)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+1),stib(xtstrp(0)+1)-1)
Q_ERRT
call qdkar(mflag(mflaty%nsubm),jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
dmsg=stxb(1:ii)//achar(arsbr)//achar(alf)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
end if
if(mflag(mflaty%tskt).gt.0)then
ii=0
call qcbxb(ii,2)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+2),stib(xtstrp(0)+2)-1)
Q_ERRT
call qdkar(mflag(mflaty%npskt)+mflag(mflaty%nvskt),jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
call qcbxb(ii,3)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+21),stib(xtstrp(0)+21)-1)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+3),stib(xtstrp(0)+3)-1)
Q_ERRT
if(cflag(confi%subm).ne.0)then
call qcbxb(ii,1)
Q_ERRT
call qdkar(mflag(mflaty%npskt),jj)
Q_ERRT
else
call qdkar(mflag(mflaty%tpskt),jj)
Q_ERRT
end if
call qctxbz(ii,jj)
Q_ERRT
if(mflag(mflaty%pninskt).ne.0)then
call qcbxb(ii,1)
Q_ERRT
stxb(ii:ii)=achar(aplus)
end if
if(cflag(confi%subm).ne.0)then
call qcbxb(ii,2)
Q_ERRT
stxb(ii:ii)=achar(alsbr)
call qdkar(mflag(mflaty%tpskt),jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
end if
call qctxb(ii,stib(xtstrl(0)+4),stib(xtstrp(0)+4)-1)
Q_ERRT
if(cflag(confi%subm).ne.0)then
call qcbxb(ii,1)
Q_ERRT
call qdkar(mflag(mflaty%nvskt),jj)
Q_ERRT
else
call qdkar(mflag(mflaty%tvskt),jj)
Q_ERRT
end if
call qctxbz(ii,jj)
Q_ERRT
if(mflag(mflaty%vninskt).ne.0)then
call qcbxb(ii,1)
Q_ERRT
stxb(ii:ii)=achar(aplus)
end if
if(cflag(confi%subm).ne.0)then
call qcbxb(ii,2)
Q_ERRT
stxb(ii:ii)=achar(alsbr)
call qdkar(mflag(mflaty%tvskt),jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
call qcbxb(ii,1)
Q_ERRT
stxb(ii:ii)=achar(arsbr)
end if
dmsg=stxb(1:ii)//achar(alf)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
end if
do i1=1,2
nps(:)=0
do i2=1,nphi
if((i1.eq.1).and.&
(stib(tpc(0)+i2).eq.phity%ext))then
cycle
else if((i1.eq.2).and.&
(stib(tpc(0)+i2).ne.phity%ext))then
cycle
end if
if(i2.lt.stib(link(0)+i2))then
if(stib(antiq(0)+i2).eq.0)then
nps(2)=nps(2)+1
else
nps(4)=nps(4)+1
end if
else if(i2.eq.stib(link(0)+i2))then
if(stib(antiq(0)+i2).eq.0)then
nps(1)=nps(1)+1
else
nps(3)=nps(3)+1
end if
end if
end do
nps(0)=nps(1)+nps(2)+nps(3)+nps(4)
if((nps(0).gt.0).or.&
(i1.eq.1))then
ii=0
call qcbxb(ii,2)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+4+i1),stib(xtstrp(0)+4+i1)-1)
Q_ERRT
call qdkar(nps(0),jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
call qcbxb(ii,3)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+21),stib(xtstrp(0)+21)-1)
Q_ERRT
if(nps(0).gt.0)then
do i2=1,4
if(nps(i2).gt.0)then
j1=stib(xtstrp(0)+6+i2)
j2=stib(xtstrl(0)+6+i2)
call qctxb(ii,j2,j1-1)
Q_ERRT
call qdkar(nps(i2),jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
end if
end do
end if
if(ii.ge.srec)then
j1=stib(xtstrp(0)+34)
j2=stib(xtstrl(0)+34)
ii=srec-j2-2
call qctxb(ii,j2,j1-1)
Q_ERRT
end if
dmsg=stxb(1:ii)//achar(alf)//achar(anull)
call qdwout(output_unit,sdrec,leftab)
Q_ERRT
end if
if(i1.eq.1)then
if(nps(0).eq.0)then
qerrt(0)=qerrty%ale
call qmfmsg(27,0,0)
Q_ERRT
end if
end if
end do
ii=0
call qcbxb(ii,2)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+11),stib(xtstrp(0)+11)-1)
Q_ERRT
call qdkar(nvert,jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
call qcbxb(ii,3)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+22),stib(xtstrp(0)+22)-1)
Q_ERRT
j1=ii
j2=ii+3
do i1=mrho,nrho
if(stib(nivd(0)+i1).gt.0)then
j3=ii
if(j1.lt.ii)then
call qcbxb(ii,2)
Q_ERRT
end if
call qdkar(i1,jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+23),stib(xtstrp(0)+23)-1)
Q_ERRT
call qdkar(stib(nivd(0)+i1),jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
end if
end do
call qctxb(ii,stib(xtstrl(0)+24),stib(xtstrp(0)+24)-1)
Q_ERRT
dmsg(1:ii+1)=stxb(1:ii)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
dmsg(1:sdrec+3)=achar(alf)//sthb1(1:sdrec)//achar(alf)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
jflag(jflaty%scstg)=4
go to 99
41 continue
ggx=rho(-1)+2*(loopx(4)-1)
ii=-2
do i1=mrho,nrho
if(stib(nivd(0)+i1).gt.0)then
ii=qwztos(i1)+stib(xtstrl(0)+23)+ii
Q_ERRT
ii=qwztos(ggx/(i1-2))+2+ii
Q_ERRT
end if
end do
lrtab(3)=ii
jj=5
i2=stib(xtstrl(0)+13)
j1=stib(xtstrl(0)+21)
j5=abs(i2-lrtab(3))/2
if(lrtab(3).lt.i2)then
j4=j5
else
j4=0
end if
lrtab(2)=j4+14
if(jflag(jflaty%scstg).lt.5)then
j3=(j5-j4)+5
jj=lrtab(3)-i2+2*jj+j1+j4-j3+3+(loopx(4)/3)
i1=stib(xtstrp(0)+13)
i5=stib(xtstrp(0)+12)
i6=(i5-1)+stib(xtstrl(0)+12)
jj=jj+(loopx(4)/2)
lrtab(1)=i6-i5-1
if(dflag(dflaty%topo).eq.0)then
i3=stib(xtstrp(0)+14)
j5=i3-1+stib(xtstrl(0)+14)
else
i3=stib(xtstrp(0)+15)
j5=i3-1+stib(xtstrl(0)+15)
end if
lrtab(4)=(i6-i5+1)+j3+i2+jj+(j5-i3+1)
if((loopx(1).eq.loopx(2)).or.&
(mrho.eq.nrho).or.&
(jflag(jflaty%noga).ne.0))then
dmsg=stcb(i5:i6)//blak(1:j3)//stcb(i1:i1-1+i2)//blak(1:jj)//stcb(i3:j5)//achar(alf)//&
achar(anull)
else
subt=1
j1=stib(xtstrp(0)+16)
j2=(j1-1)+stib(xtstrl(0)+16)
dmsg=stcb(i5:i6)//blak(1:j3)//stcb(i1:i1-1+i2)//blak(1:jj)//stcb(i3:j5)//blak(1:8)//&
stcb(j1:j2)//achar(alf)//achar(anull)
lrtab(4)=lrtab(4)+8+3
end if
call qdwout(output_unit,qerrl0,leftab)
Q_ERRT
end if
if(wot.eq.4)then
go to 99
end if
51 continue
if(jflag(jflaty%noga).gt.0)then
i5=stib(xtstrp(0)+25)
i6=(i5-1)+stib(xtstrl(0)+25)
dmsg=stcb(i5:i6)//achar(anull)
else
call qdkar(nloop,jj)
Q_ERRT
dmsg=blak(1:lrtab(1)-jj)//zstr(1:jj)//achar(anull)
end if
call qdwout(output_unit,sdrec,0)
Q_ERRT
jflag(jflaty%scstg)=5
go to 99
61 continue
ggx=rho(-1)+2*(loopx(4)-1)
ii=0
if((jflag(jflaty%noga).ne.0).or.&
(jflag(jflaty%nogc).ne.0))then
kk=lrtab(3)/2
call qcbxb(ii,kk)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+27),stib(xtstrp(0)+27)-1)
Q_ERRT
kk=kk-1
call qcbxb(ii,lrtab(3)-kk)
Q_ERRT
else
do i1=mrho,nrho
if(stib(nivd(0)+i1).gt.0)then
kk=qwztos(ggx/(i1-2))+2
Q_ERRT
call qdkar(i1,jj)
Q_ERRT
if(rho(i1).gt.0)then
call qctxbz(ii,jj)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+23),stib(xtstrp(0)+23)-1)
Q_ERRT
call qdkar(rho(i1),jj)
Q_ERRT
call qctxbz(ii,jj)
Q_ERRT
kk=kk-jj
else
call qcbxb(ii,jj)
Q_ERRT
call qctxb(ii,stib(xtstrl(0)+26),stib(xtstrp(0)+26)-1)
Q_ERRT
end if
call qcbxb(ii,kk)
Q_ERRT
end if
end do
end if
ii=ii-2
jj=5
if(jflag(jflaty%noga).eq.0)then
if(jflag(jflaty%nogc).eq.0)then
if(jflag(jflaty%nogp).eq.0)then
call qcbxb(ii,jj+jflag(jflaty%scppar))
Q_ERRT
jflag(jflaty%scppar)=1-jflag(jflaty%scppar)
call qctxb(ii,stib(xtstrl(0)+21),stib(xtstrp(0)+21)-1)
Q_ERRT
jj=6
call qcbxb(ii,jj+jflag(jflaty%scppar))
Q_ERRT
call qctxb(ii,qcol(dcoty%part),qcop(dcoty%part))
Q_ERRT
if(cflag(confi%maxc).lt.0)then
call qctxb(ii,stib(xtstrl(0)+28),stib(xtstrp(0)+28)-1)
Q_ERRT
end if
end if
end if
end if
dmsg=blak(1:lrtab(2))//stxb(1:ii)//achar(anull)
call qdwout(output_unit,qerrl0,leftab)
Q_ERRT
jflag(jflaty%scstg)=6
go to 99
71 continue
if(subt.ne.0)then
ii=0
call qctxb(ii,qcol(dcoty%loop),qcop(dcoty%loop))
Q_ERRT
if(cflag(confi%maxc).lt.0)then
call qctxb(ii,stib(xtstrl(0)+28),stib(xtstrp(0)+28)-1)
Q_ERRT
end if
dmsg=blak(1:lrtab(4))//stxb(1:ii)//achar(anull)
call qdwout(output_unit,qerrl0,leftab)
Q_ERRT
jflag(jflaty%scstg)=5
end if
go to 99
81 continue
ii=0
if(cflag(confi%maxc).lt.0)then
call qctxb(ii,stib(xtstrl(0)+18),stib(xtstrp(0)+18)-1)
Q_ERRT
else
call qctxb(ii,stib(xtstrl(0)+17),stib(xtstrp(0)+17)-1)
Q_ERRT
end if
call qctxb(ii,stib(xtstrl(0)+21),stib(xtstrp(0)+21)-1)
Q_ERRT
call qcbxb(ii,3)
Q_ERRT
call qctxb(ii,qcol(dcoty%nat),qcop(dcoty%nat))
Q_ERRT
jj=0
if(qcol(dcoty%nat).eq.1)then
j1=qcop(dcoty%nat)+1
if(iachar(stcb(j1:j1))-1.eq.azero)then
jj=1
end if
end if
if(dflag(dflaty%topo).eq.0)then
call qctxb(ii,stib(xtstrl(0)+19)-jj,stib(xtstrp(0)+19)-1)
Q_ERRT
else
call qctxb(ii,stib(xtstrl(0)+20)-jj,stib(xtstrp(0)+20)-1)
Q_ERRT
end if
if(cflag(confi%noopt).eq.0)then
if((jflag(jflaty%noga).ne.0).or.&
((jflag(jflaty%nogc).ne.0).and.(loopx(3).eq.loopx(4))))then
call qctxb(ii,stib(xtstrl(0)+28),stib(xtstrp(0)+28)-1)
Q_ERRT
end if
end if
if(cflag(confi%dspl).lt.dsplmod%dbg)then
if(cflag(confi%msg).lt.0)then
if(jflag(jflaty%nw).gt.0)then
call qctxb(ii,stib(xtstrl(0)+29),stib(xtstrp(0)+29)-1)
Q_ERRT
end if
end if
end if
lrtab(5)=8
j1=2-subt
j2=lrtab(5)+ii+3+j1
dmsg(1:1)=achar(alf)
dmsg(j1:j2)=achar(alf)//blak(1:lrtab(5))//stxb(1:ii)//achar(alf)//achar(alf)//achar(anull)
call qdwout(output_unit,sdrec,0)
Q_ERRT
if((jflag(jflaty%nw).eq.0).or.&
(cflag(confi%dspl).eq.dsplmod%info))then
flush(unit=output_unit)
end if
99 continue
if(wot.eq.0)then
if(qerrt(1).ne.qerrty%ok)then
qerrt(0)=qerrt(1)
qerrt(1)=qerrty%ok
end if
end if
return
end subroutine qsp
subroutine qrflag0
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::tr=1
integer(kind=c_int_least32_t),parameter::ntr=2
integer(kind=c_int_least32_t),parameter::sb=3
integer(kind=c_int_least32_t),parameter::nsb=4
integer(kind=c_int_least32_t),parameter::rb=5
integer(kind=c_int_least32_t),parameter::nrb=6
integer(kind=c_int_least32_t),parameter::b=7
integer(kind=c_int_least32_t),parameter::nb=8
integer(kind=c_int_least32_t),parameter::sl=9
integer(kind=c_int_least32_t),parameter::nsl=10
integer(kind=c_int_least32_t),parameter::dl=11
integer(kind=c_int_least32_t),parameter::ndl=12
integer(kind=c_int_least32_t)::intf(1:12)
integer(kind=c_int_least32_t)::ii,i1,i2,j1,j2
if(nphi.eq.1)then
mflag(mflaty%one)=1
end if
j1=0
j2=0
do i1=1,nphi
if(stib(antiq(0)+i1).eq.0)then
j1=1
else
j2=1
end if
end do
if(j1.eq.0)then
mflag(mflaty%cac)=-1
else if(j2.eq.0)then
mflag(mflaty%cac)=1
end if
mflag(mflaty%even)=1
do i1=1,nvert
if(modulo(stib(vval(0)+i1),2).ne.0)then
mflag(mflaty%even)=0
exit
end if
end do
mflag(mflaty%fpath)=1
do i1=1,nvert
j1=stib(vparto(0)+i1)
j2=j1+stib(vval(0)+i1)
ii=-1
do i2=j1+1,j2
ii=ii+stib(antiq(0)+stib(i2))
end do
if(abs(ii).ne.1)then
mflag(mflaty%fpath)=0
exit
end if
end do
if(mflag(mflaty%one).eq.0)then
jflag(jflaty%noaut)=0
else if(mflag(mflaty%vdup).ne.0)then
jflag(jflaty%noaut)=0
else
jflag(jflaty%noaut)=1
end if
if(mflag(mflaty%even).ne.0)then
if(modulo(nleg,2).ne.0)then
jflag(jflaty%noga)=1
end if
end if
if(nleg.eq.1)then
if(stib(tpc(0)+stib(leg(0)+1)).eq.phity%notdp)then
jflag(jflaty%noga)=1
end if
end if
if(dflag(dflaty%plink).ne.0)then
if((dflag(dflaty%nob).gt.0).or.&
(dflag(dflaty%norb).gt.0))then
j1=stib(tftic(0)+opety%plink)
do i1=stib(tfta(0)+j1),stib(tftb(0)+j1)
if(stib(tftyp(0)+stib(tf2(0)+i1)).gt.0)then
jflag(jflaty%noga)=1
end if
end do
end if
end if
if(dflag(dflaty%topo).ne.0)then
if(mflag(mflaty%one).eq.0)then
qerrmsg(1:srec)="option 'topol' does not apply here"//achar(anull)
qerrt(0)=qerrty%inp
call qmput(0,0,0)
Q_ERRT
end if
end if
if(dflag(dflaty%newa).ne.0)then
ii=dflag(dflaty%topo)+dflag(dflaty%newe)+dflag(dflaty%newt)+dflag(dflaty%newp)+dflag(dflaty%newc)-1
if(ii.gt.0)then
qerrt(0)=qerrty%inp
call qcfmsg(32,0,0)
Q_ERRT
end if
end if
dflag(dflaty%newt)=max(dflag(dflaty%newt),dflag(dflaty%topo))
if(dflag(dflaty%fl).ne.0)then
if((mflag(mflaty%cac).gt.0).or.&
(mflag(mflaty%fpath).eq.0))then
qerrt(0)=qerrty%inp
call qcfmsg(32,0,0)
Q_ERRT
end if
end if
if(jflag(jflaty%intlp).eq.0)then
if(dflag(dflaty%norb).ne.0)then
jflag(jflaty%intlp)=1
else if(dflag(dflaty%onshx).ne.0)then
jflag(jflaty%intlp)=1
else if(dflag(dflaty%nosig).ne.0)then
jflag(jflaty%intlp)=1
else if(dflag(dflaty%cyc).ne.0)then
jflag(jflaty%intlp)=1
else if(dflag(dflaty%ovi).ne.0)then
jflag(jflaty%intlp)=1
else if(dflag(dflaty%plink).ne.0)then
jflag(jflaty%intlp)=1
end if
end if
if(cflag(confi%noopt).ne.0)then
go to 99
end if
intf(:)=0
if(dflag(dflaty%nob).ne.0)then
if(dflag(dflaty%nob).gt.0)then
intf(nrb)=1
intf(nsb)=1
intf(nb)=1
else
intf(b)=1
end if
end if
if(dflag(dflaty%norb).ne.0)then
if(dflag(dflaty%norb).gt.0)then
intf(nrb)=1
else
intf(rb)=1
intf(b)=1
end if
end if
if(dflag(dflaty%nosb).ne.0)then
if(dflag(dflaty%nosb).gt.0)then
intf(nsb)=1
else
intf(sb)=1
intf(b)=1
end if
end if
if(dflag(dflaty%edge).lt.0)then
intf(b)=1
if(loopx(3).gt.0)then
jflag(jflaty%noga)=1
end if
end if
if(dflag(dflaty%onsh).ne.0)then
if(dflag(dflaty%onsh).lt.0)then
intf(b)=1
end if
end if
if(dflag(dflaty%nosn).ne.0)then
if(dflag(dflaty%nosn).gt.0)then
intf(nsb)=1
intf(nsl)=1
end if
end if
if(dflag(dflaty%cyc).ne.0)then
if(dflag(dflaty%cyc).lt.0)then
intf(ntr)=1
end if
end if
if(dflag(dflaty%bip).ne.0)then
if(dflag(dflaty%bip).gt.0)then
intf(nsl)=1
end if
end if
if(dflag(dflaty%nosl).ne.0)then
if(dflag(dflaty%nosl).gt.0)then
intf(nsl)=1
else
intf(sl)=1
intf(ntr)=1
end if
end if
if(dflag(dflaty%nodl).ne.0)then
if(dflag(dflaty%nodl).lt.0)then
intf(dl)=1
intf(ntr)=1
end if
end if
if(dflag(dflaty%nopa).ne.0)then
if(dflag(dflaty%nopa).gt.0)then
intf(ndl)=1
else
intf(ntr)=1
end if
end if
if(dflag(dflaty%simp).ne.0)then
if(dflag(dflaty%simp).gt.0)then
intf(nsl)=1
intf(ndl)=1
else
intf(ntr)=1
end if
end if
if((intf(tr).ne.0).and.&
(intf(ntr).ne.0))then
jflag(jflaty%noga)=1
else if((intf(sb).ne.0).and.&
(intf(nsb).ne.0))then
jflag(jflaty%noga)=1
else if((intf(rb).ne.0).and.&
(intf(nrb).ne.0))then
jflag(jflaty%noga)=1
else if((intf(b).ne.0).and.&
(intf(nb).ne.0))then
jflag(jflaty%noga)=1
else if((intf(sl).ne.0).and.&
(intf(nsl).ne.0))then
jflag(jflaty%noga)=1
else if((intf(dl).ne.0).and.&
(intf(ndl).ne.0))then
jflag(jflaty%noga)=1
end if
if(dflag(dflaty%nob).lt.0)then
if(dflag(dflaty%norb).gt.0)then
if(dflag(dflaty%nosb).gt.0)then
jflag(jflaty%noga)=1
end if
end if
end if
if(dflag(dflaty%onsh).lt.0)then
if(dflag(dflaty%onshx).gt.0)then
jflag(jflaty%noga)=1
end if
end if
if(dflag(dflaty%cyc).gt.0)then
if(dflag(dflaty%nob).gt.0)then
if(dflag(dflaty%ovi).lt.0)then
jflag(jflaty%noga)=1
end if
end if
end if
if(dflag(dflaty%cyc).lt.0)then
if(dflag(dflaty%nosn).gt.0)then
if(dflag(dflaty%nob).gt.0)then
if(dflag(dflaty%ovi).gt.0)then
jflag(jflaty%noga)=1
end if
end if
end if
end if
if(dflag(dflaty%onsh).lt.0)then
if(dflag(dflaty%ovi).gt.0)then
if(dflag(dflaty%simp).gt.0)then
jflag(jflaty%noga)=1
end if
end if
end if
if(dflag(dflaty%nodl).gt.0)then
if(dflag(dflaty%nosl).gt.0)then
if(dflag(dflaty%simp).lt.0)then
jflag(jflaty%noga)=1
end if
end if
end if
if(dflag(dflaty%nodl).gt.0)then
if(dflag(dflaty%nosl).gt.0)then
if(dflag(dflaty%nopa).lt.0)then
jflag(jflaty%noga)=1
end if
end if
end if
if(dflag(dflaty%nopa).lt.0)then
if(dflag(dflaty%simp).gt.0)then
jflag(jflaty%noga)=1
end if
end if
99 continue
return
end subroutine qrflag0
subroutine qrflag
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::i1
jflag(jflaty%nogc)=0
if(nloop.gt.0)then
if(dflag(dflaty%nob).lt.0)then
if(dflag(dflaty%ovi).gt.0)then
if(dflag(dflaty%nosn).gt.0)then
jflag(jflaty%nogc)=1
else if(dflag(dflaty%simp).gt.0)then
jflag(jflaty%nogc)=1
end if
end if
end if
end if
if(nloop.gt.1)then
if(dflag(dflaty%cyc).gt.0)then
if(dflag(dflaty%nob).lt.0)then
if(dflag(dflaty%ovi).gt.0)then
jflag(jflaty%nogc)=1
end if
end if
end if
if(dflag(dflaty%cyc).gt.0)then
if(dflag(dflaty%nosl).lt.0)then
jflag(jflaty%nogc)=1
end if
end if
end if
if(nloop.eq.0)then
if(dflag(dflaty%nob).gt.0)then
if(nrho.lt.nleg)then
jflag(jflaty%nogc)=1
end if
end if
if(dflag(dflaty%norb).gt.0)then
if(nrho.lt.nleg)then
jflag(jflaty%nogc)=1
end if
end if
if(dflag(dflaty%nosb).lt.0)then
jflag(jflaty%nogc)=1
end if
if(dflag(dflaty%nosn).lt.0)then
jflag(jflaty%nogc)=1
end if
if(dflag(dflaty%cyc).lt.0)then
jflag(jflaty%nogc)=1
end if
if(dflag(dflaty%bip).lt.0)then
jflag(jflaty%nogc)=1
end if
if(dflag(dflaty%nosl).lt.0)then
jflag(jflaty%nogc)=1
end if
if(dflag(dflaty%nodl).lt.0)then
jflag(jflaty%nogc)=1
end if
if(dflag(dflaty%nopa).lt.0)then
jflag(jflaty%nogc)=1
end if
if(dflag(dflaty%fl).lt.0)then
jflag(jflaty%nogc)=1
end if
if(dflag(dflaty%simp).lt.0)then
jflag(jflaty%nogc)=1
end if
else if(nloop.eq.1)then
if(dflag(dflaty%cyc).lt.0)then
jflag(jflaty%nogc)=1
end if
end if
do i1=0,maxli
zpro(i1)=abs(zpro(i1))
zcho(i1)=abs(zcho(i1))
zbri(i1)=abs(zbri(i1))
rbri(i1)=abs(rbri(i1))
sbri(i1)=abs(sbri(i1))
end do
if(dflag(dflaty%nob).gt.0)then
do i1=1,maxli
rbri(i1)=-rbri(i1)
sbri(i1)=-sbri(i1)
zbri(i1)=-zbri(i1)
end do
else if(dflag(dflaty%nob).lt.0)then
zbri(0)=-zbri(0)
end if
if(dflag(dflaty%norb).gt.0)then
do i1=1,maxli
rbri(i1)=-rbri(i1)
end do
else if(dflag(dflaty%norb).lt.0)then
rbri(0)=-rbri(0)
end if
if(dflag(dflaty%nosb).gt.0)then
do i1=1,maxli
sbri(i1)=-sbri(i1)
end do
else if(dflag(dflaty%nosb).lt.0)then
sbri(0)=-sbri(0)
end if
if(dflag(dflaty%onsh).lt.0)then
zbri(0)=-zbri(0)
end if
if(dflag(dflaty%nosn).gt.0)then
do i1=1,maxli
sbri(i1)=-sbri(i1)
end do
end if
if(zcho(0).gt.0)then
if(dflag(dflaty%nosb).lt.0)then
zcho(0)=-1
else if(dflag(dflaty%onsh).lt.0)then
zcho(0)=-1
else if(dflag(dflaty%onshx).lt.0)then
zcho(0)=-1
else if(dflag(dflaty%nosig).lt.0)then
zcho(0)=-1
else if(dflag(dflaty%nosn).lt.0)then
zcho(0)=-1
else if(dflag(dflaty%simp).lt.0)then
zcho(0)=-1
end if
end if
99 continue
return
end subroutine qrflag
subroutine qpropos
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qsty
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
#ifdef Q_API
use,non_intrinsic::q_api
#endif
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstdz
integer(kind=c_int_least32_t),parameter::dtzl0=16
character(kind=asciik,len=dtzl0),target::dtz(1:3)
character(kind=asciik,len=:),pointer::dtzp
integer(kind=c_int_least32_t)::d0,f0,f1,f2,ip,stwbp,stwbq,stwbu,dtzl
integer(kind=c_int_least32_t)::ig,igc,igk,igut,kma,lupi,lupj,lupt,sec
integer(kind=c_int_least32_t)::i1,i2,ij,j1,j2,jj,jk,k1,k2,ier,p1
ier=0
if((jflag(jflaty%ingg).eq.0).or.&
(qxmod.eq.qmod%api))then
if(qxmod.eq.qmod%auto)then
do i1=1,nfiles
if(filt(i1).eq.qfty%otyp)then
if(filp(i1).ne.nap)then
call qopen(i1)
Q_ERRT
fild(i1)=qfdty%dok
end if
end if
end do
end if
j1=min(dekc%sty,dekc%outp)
i1=1
d0=0
do while(i1.lt.j1)
d0=d0+comc(i1)
i1=i1+1
end do
else if(jflag(jflaty%ingg).ne.-1)then
ier=1
end if
if(ier.eq.0)then
sec=1-2*jflag(jflaty%ingg)
ig=iogp(sec)
if(ig.ge.iogp(sec+1))then
ier=1
end if
end if
if(ier.ne.0)then
go to 80
end if
f0=0
10 continue
if(f0.ge.nfiles)then
go to 99
end if
f0=f0+1
if(filt(f0).ne.qfty%otyp)then
if(filt(f0).ne.qfty%ptyp)then
go to 10
end if
end if
if(qxmod.eq.qmod%api)then
ig=ig+2
else if(filp(f0).ne.nap)then
ig=ig+2
else
ig=ig+stib(ig+1)
go to 10
end if
f1=filo(f0)
f2=film(f0)
p1=nap
serrt=qerrty%ok
if(f1.lt.1)then
serrt=qerrty%q
else if(f1.gt.nsfiles)then
serrt=qerrty%q
else if(stib(ig-2).ne.eosf)then
serrt=qerrty%q
else if((filt(f0).ne.qfty%otyp).and.&
(filt(f0).ne.qfty%ptyp))then
serrt=qerrty%q
end if
if(f1.lt.nsfiles)then
if(stib(ig-2+stib(ig-1)).ne.eosf)then
serrt=qerrty%q
end if
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qpropos_3'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
if((jflag(jflaty%ingg).eq.0).or.&
(qxmod.eq.qmod%api))then
stwbqf(f1)=stwbpf(f1)
end if
if(qxmod.eq.qmod%api)then
#ifdef Q_API
if(obsel(f1).eq.qisgnl%n)then
call qpout(f0)
Q_ERRT
ig=(ig-1)+(stib(ig-1)-1)
go to 10
end if
#endif
else if(jflag(jflaty%ingg).lt.0)then
if(stwbqf(f1).gt.stwbpf(f1))then
if(filt(f0).eq.qfty%otyp)then
call qout(f0)
Q_ERRT
stwbqf(f1)=stwbpf(f1)
else
qerrmsg(1:srec)='qpropos_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
end if
stwbp=stwbpf(f1)
stwbq=stwbqf(f1)
stwbu=stwbuf(f1)
kma=-1
lupt=0
20 continue
igk=stib(ig)
if(igk.gt.0)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(igk)
ig=ig+1
go to 20
else if(igk.eq.eosf)then
if(lupt.ne.0)then
go to 80
end if
if(filt(f0).eq.qfty%ptyp)then
#ifdef Q_API
stwbqf(f1)=stwbq
call qpout(f0)
Q_ERRT
#endif
else if(stwbq.gt.stwbp)then
stwbqf(f1)=stwbq
call qout(f0)
Q_ERRT
stwbqf(f1)=stwbpf(f1)
end if
if(jflag(jflaty%ingg).lt.0)then
if(filt(f0).eq.qfty%otyp)then
call qclose(f0)
Q_ERRT
end if
end if
go to 10
else if(igk.eq.eoa)then
qerrmsg(1:srec)='qpropos_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
igc=stib(ig+1)
if(igk.eq.-1)then
if(igc.eq.stylo%sto)then
70 continue
if(stib(ig+4).eq.0)then
stib(ig+4)=ncom
stib(ig+5)=1
else
stib(ig+5)=stib(ig+5)+1
end if
if(stib(ig+4).lt.stib(ig+5))then
stib(ig+4)=0
ig=ig+1
lupt=0
lupi=0
else
lupt=stylo%sto
lupi=stib(ig+5)
if(lupi.gt.d0)then
if(qxmod.eq.qmod%auto)then
jk=2
else
jk=1
end if
if(lupi.le.d0+jk*nsfiles)then
if((lupi.lt.d0+jk*(f2-1)+1).or.&
(lupi.gt.d0+jk*f2))then
go to 70
end if
end if
end if
end if
else if(igc.eq.stylo%sti)then
if(stib(ig+4).eq.0)then
stib(ig+4)=stib(frecc(0)+lupi)
stib(ig+5)=stib(irecc(0)+lupi)
else
stib(ig+5)=stib(ig+5)+1
end if
if(stib(ig+4).lt.stib(ig+5))then
stib(ig+4)=0
ig=ig+1
lupt=stylo%sto
lupj=0
else
lupt=stylo%sti
lupj=stib(ig+5)
end if
else if((igc.eq.stylo%i).or.&
(igc.eq.stylo%o))then
lupt=igc
if(stib(ig+4).eq.0)then
if(lupt.eq.stylo%i)then
stib(ig+4)=inco
stib(ig+5)=0
else if(lupt.eq.stylo%o)then
stib(ig+4)=nleg
stib(ig+5)=inco
end if
end if
stib(ig+5)=stib(ig+5)+1
if(stib(ig+4).lt.stib(ig+5))then
stib(ig+4)=0
lupt=0
ig=ig+1
else
if(lupt.eq.stylo%r)then
lupj=stib(ig+5)
else
lupi=stib(ig+5)
end if
end if
else if(igc.ne.stylo%end)then
go to 80
end if
else if(igk.eq.-2)then
if(igc.eq.22)then
if(jflag(jflaty%backmod).eq.0)then
if(kma.ge.0)then
stwbq=kma
kma=-1
end if
else if(stwbq.gt.stwbp)then
stwbq=stwbq-1
else
go to 80
end if
else
go to 80
end if
else if(igk.eq.-3)then
ip=stwbq+1
if(igc.lt.80)then
if(igc.eq.77)then
j2=nleg
else if(igc.eq.78)then
j2=inco
else if(igc.eq.79)then
j2=outg
else if(igc.eq.67)then
j2=loopx(1)
else if(igc.eq.68)then
j2=loopx(2)
else
go to 80
end if
call qdkar(j2,j1)
Q_ERRT
stwbq=stwbq+j1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:j1)
else
if(igc.eq.80)then
if(sec.eq.1)then
stwbq=stwbq+qcol(dcoty%off)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(qcop(dcoty%off)+1:qcop(dcoty%off)+qcol(dcoty%off))
else
stwbq=stwbq+qcol(dcoty%nat)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(qcop(dcoty%nat)+1:qcop(dcoty%nat)+qcol(dcoty%nat))
end if
else if(igc.eq.81)then
stwbq=stwbq+qcol(dcoty%nat)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(qcop(dcoty%nat)+1:qcop(dcoty%nat)+qcol(dcoty%nat))
else if(igc.eq.82)then
stwbq=stwbq+qcol(dcoty%offix)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(qcop(dcoty%offix)+1:qcop(dcoty%offix)+qcol(dcoty%offix))
else if(igc.eq.84)then
stwbq=stwbq+qvl
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(qvp:(qvp-1)+qvl)
else if(abs(igc-84).eq.1)then
call date_and_time(date=dtz(1),time=dtz(2),zone=dtz(3))
j2=stwbq
do i1=1,3
dtzl=0
do i2=len(dtz(i1)),1,-1
if(iachar(dtz(i1)(i2:i2)).ne.aspc)then
dtzl=i2
exit
end if
end do
if(dtzl.gt.0)then
if((i1.eq.1).and.&
(dtzl.eq.8))then
j1=qstdz(dtz(1),1,8,inty%l)
Q_ERRT
else if((i1.eq.2).and.&
(dtzl.eq.10))then
j1=qstdz(dtz(2),1,6,inty%l)
Q_ERRT
if(j1.ne.0)then
j1=qstdz(dtz(2),8,10,inty%s)
Q_ERRT
end if
else
j1=0
end if
ip=stwbq+1
stwbq=ip+dtzl
if(j1.gt.0)then
if(igc.eq.83)then
stwbq=stwbq+2
end if
end if
if(stwbq.gt.stwbu)then
go to 85
end if
if((igc.eq.85).or.&
(j1.eq.0))then
dtzp=>dtz(i1)
stwb(ip:stwbq)=dtzp(1:dtzl)//achar(aspc)
else if(i1.eq.1)then
stwb(ip:stwbq)=dtz(1)(1:4)//achar(aslash)//dtz(1)(5:6)//achar(aslash)//dtz(1)(7:8)//achar(aspc)
else if(i1.eq.2)then
stwb(ip:stwbq)=dtz(2)(1:2)//achar(acol)//dtz(2)(3:4)//achar(acol)//dtz(2)(5:10)//achar(aspc)
end if
end if
end do
if(j2.lt.stwbq)then
stwbq=stwbq-1
end if
else if(igc.eq.86)then
if(stib(momel(0)).gt.0)then
stwbq=stwbq+stib(momel(0))
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(stib(momep(0)):stib(momeq(0)))
end if
else if(igc.eq.87)then
if(stib(momzl(0)).gt.0)then
stwbq=stwbq+momzl(0)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(momzp(0):momzq(0))
end if
else
go to 80
end if
end if
else if(igk.eq.-4)then
if(igc.lt.60)then
if(igc.lt.40)then
if(abs(igc-32).eq.1)then
k1=lupi
ij=stib(leg(0)+k1)
if(igc.eq.31)then
ij=stib(link(0)+ij)
end if
if(lupi.gt.inco)then
ij=stib(link(0)+ij)
end if
k2=stib(namel(0)+ij)
ip=stwbq+1
stwbq=stwbq+k2
if(stwbq.gt.stwbu)then
go to 85
end if
j1=stib(namep(0)+ij)
stwb(ip:stwbq)=stcb(j1:j1-1+k2)
else if(abs(igc-36).eq.1)then
k1=lupi
if(igc.eq.37)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(aminus)
end if
ip=stwbq+1
stwbq=stwbq+stib(momel(0)+k1)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(stib(momep(0)+k1):stib(momeq(0)+k1))
else if(igc.eq.32)then
k1=lupi
ij=stib(leg(0)+k1)
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
if(stib(antiq(0)+ij).eq.0)then
stwb(stwbq:stwbq)=achar(aplus)
else
stwb(stwbq:stwbq)=achar(aminus)
end if
else if(igc.eq.34)then
k1=lupi
if(k1.gt.inco)then
jj=2
else
jj=1
end if
j1=stib(xstypp(0)+jj)
j2=stib(xstypl(0)+jj)
ip=stwbq+1
stwbq=stwbq+j2
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(j1:j1+(j2-1))
else
go to 80
end if
else if(igc.lt.50)then
if(igc.eq.40)then
k1=lupi
if(k1.gt.inco)then
jj=2
else
jj=1
end if
else if(igc.eq.42)then
k1=lupi
if(k1.gt.inco)then
jj=2*(inco-k1)
else
jj=1-2*k1
end if
else
go to 80
end if
call qdkar(jj,jk)
Q_ERRT
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
else if(igc.lt.60)then
if(igc.eq.52)then
k1=lupi
else if(igc.eq.53)then
k1=lupi-inco
else if(igc.eq.54)then
k1=lupi
else if(igc.eq.55)then
if(lupi.gt.inco)then
k1=2*(lupi-inco)
else
k1=2*lupi-1
end if
else
go to 80
end if
call qdkar(k1,jk)
Q_ERRT
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
else
go to 80
end if
else if(igc.eq.90)then
if(lupt.eq.stylo%sto)then
k1=stib(irecc(0)+lupi)
k2=stib(frecc(0)+lupi)
else if(lupt.eq.stylo%sti)then
k1=lupj
k2=lupj
else
go to 80
end if
if(p1.ne.nap)then
do while(stib(p1+5).lt.k1)
p1=stib(p1)
end do
else
p1=rlink
end if
do i1=k1,k2
j1=stib(p1+1)
j2=stib(p1+2)-1
ip=stwbq+1
stwbq=stwbq+j2
if(stwbq.gt.stwbu)then
go to 85
end if
serrt=qerrty%ok
if(j2.lt.1)then
serrt=qerrty%q
end if
j2=j1+j2
if(iachar(stcb(j2:j2)).ne.alf)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
stwb(ip:stwbq)=stcb(j1:j2-1)
if(stib(p1).gt.p1)then
p1=stib(p1)
end if
end do
else
go to 80
end if
else if(igk.eq.-6)then
if((igc.le.0).or.&
(igc.gt.nudk))then
go to 80
end if
igut=stib(udkt(0)+igc)
if(igut.eq.1)then
ij=stib(udki(0)+igc)
if((ij.le.0).or.&
(ij.gt.ngmk))then
go to 80
end if
j1=stib(gmkvp(0)+ij)
j2=stib(gmkvl(0)+ij)
if(j2.gt.0)then
ip=stwbq+1
stwbq=stwbq+j2
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(j1:j1+j2-1)
else if(j2.lt.0)then
go to 80
end if
else if(igut.eq.2)then
if(lupt.eq.stylo%i)then
k1=lupi
k2=stib(link(0)+stib(leg(0)+k1))
else if(lupt.eq.stylo%o)then
k1=lupi
k2=stib(leg(0)+k1)
else
go to 80
end if
if(stib(ig+3).ne.0)then
k2=stib(link(0)+k2)
end if
if((k2.le.0).or.&
(k2.gt.nphi))then
go to 80
end if
ij=stib(udki(0)+igc)
if((ij.le.0).or.&
(ij.gt.npmk))then
go to 80
end if
j2=stib(stib(pmkvflp(0)+k2)+ij)
if(j2.gt.0)then
ip=stwbq+1
stwbq=stwbq+j2
if(stwbq.gt.stwbu)then
go to 85
end if
j1=stib(stib(pmkvfpp(0)+k2)+ij)
stwb(ip:stwbq)=stcb(j1:j1-1+j2)
else if(j2.lt.0)then
go to 80
end if
else
go to 80
end if
else
go to 80
end if
ig=ig+stib(ig+2)
go to 20
80 continue
j1=stib(pske(0)+sec)
j2=j1-1+stib(wske(0)+sec)
qerrt(0)=qerrty%q
if(sec.eq.1)then
call qstymsg(10,0,0,0,0,0)
Q_ERRT
else
call qstymsg(12,0,0,0,0,0)
Q_ERRT
end if
85 continue
qerrt(0)=qerrty%q
#ifdef Q_API
f1x=f1
call qpomsg(3)
Q_ERRT
#else
call quput(7)
Q_ERRT
#endif
99 continue
return
end subroutine qpropos
subroutine qumpi(xx,situ)
use,non_intrinsic::qmix
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::xx
integer(kind=c_int_least32_t),intent(out)::situ
integer(kind=c_int_least32_t)::aa(1:maxn),bb(1:maxn)
integer(kind=c_int_least32_t)::i1,i2,i3,i4,ii,jj,kk
ntadp=0
situ=-1
do i1=rhop1,n
do i2=i1+1,n
if(gam(i1,i2).eq.1)then
gam(i1,i2)=0
kk=1
bb(1)=1
aa(1)=1
if(n.gt.1)then
aa(2:n)=0
end if
do i3=1,n
if(kk.eq.n)then
go to 20
end if
if(i3.gt.kk)then
gam(i1,i2)=1
if(xx.eq.1)then
go to 99
end if
ii=0
do i4=1,rho(-1)
ii=ii+aa(i4)
end do
if(xx.eq.2)then
if((ii.eq.0).or.&
(ii.eq.rho(-1)))then
go to 99
end if
else if(xx.eq.3)then
if((ii.eq.0).or.&
(ii.eq.rho(-1)))then
ntadp=ntadp+1
xtail(ntadp)=i1
xhead(ntadp)=i2
end if
else if(xx.eq.4)then
if((ii.eq.1).or.&
(ii.eq.rho(-1)-1))then
go to 99
end if
end if
go to 20
end if
jj=bb(i3)
do i4=1,jj-1
if(aa(i4).eq.0)then
if(gam(i4,jj).gt.0)then
kk=kk+1
bb(kk)=i4
aa(i4)=1
end if
end if
end do
do i4=jj+1,n
if(aa(i4).eq.0)then
if(gam(jj,i4).gt.0)then
kk=kk+1
bb(kk)=i4
aa(i4)=1
end if
end if
end do
end do
qerrmsg(1:srec)='qumpi_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
20 continue
gam(i1,i2)=1
end if
end do
end do
situ=1
99 continue
return
end subroutine qumpi
subroutine qumvi(xx,situ)
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::xx
integer(kind=c_int_least32_t),intent(out)::situ
integer(kind=c_int_least32_t)::ii,i1,i2,i3,i4,jj,j0,j1,j2,j3,kk,k1
integer(kind=c_int_least32_t)::aa(1:maxn),bb(1:maxn),cc(1:maxn)
situ=1
if(xx.eq.1)then
if(nloop.eq.0)then
go to 99
end if
ii=0
if(rho(-1).ne.1)then
ii=1
else if(nloop.gt.1)then
ii=1
end if
if(ii.ne.0)then
do i1=rhop1,n
if(gam(i1,i1).ne.0)then
go to 80
end if
end do
end if
else if(xx.eq.2)then
if(n-1-rhop1.le.0)then
go to 99
end if
else if(xx.eq.3)then
if(nloop.eq.0)then
go to 99
else if(rho(-1).eq.0)then
go to 99
end if
go to 30
else
qerrmsg(1:srec)='qumvi_0'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
d01: do i1=rhop1,n
if(xx.eq.1)then
kk=rho(-1)
do i2=1,rho(-1)
aa(i2)=1
bb(i2)=i2
end do
do i2=rhop1,n
aa(i2)=0
end do
k1=n
else if(xx.eq.2)then
kk=1
do i2=rhop1,n
aa(i2)=0
end do
if(i1.ne.rhop1)then
bb(1)=rhop1
else if(i1.ne.n)then
bb(1)=n
else
go to 99
end if
aa(bb(1))=1
k1=n-rho(-1)
end if
do i2=1,k1
if(kk.eq.k1)then
cycle d01
end if
if(i2.gt.kk)then
go to 80
end if
j1=bb(i2)
if(j1.ne.i1)then
do i3=rhop1,j1-1
if(aa(i3).eq.0)then
if(gam(i3,j1).gt.0)then
kk=kk+1
bb(kk)=i3
aa(i3)=1
end if
end if
end do
do i3=j1+1,n
if(aa(i3).eq.0)then
if(gam(j1,i3).gt.0)then
kk=kk+1
bb(kk)=i3
aa(i3)=1
end if
end if
end do
end if
end do
qerrmsg(1:srec)='qumvi_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end do d01
go to 99
30 continue
d02: do i1=rhop1,n
if(n.gt.0)then
aa(1:n)=0
end if
jj=0
kk=1
aa(i1)=-1
bb(1)=i1
d03: do i2=1,n
if(kk.eq.n)then
exit d03
else if(aa(i2).ne.0)then
cycle d03
end if
jj=jj+1
aa(i2)=jj
kk=kk+1
bb(kk)=i2
ii=kk
35 continue
j1=bb(ii)
do i3=i2+1,j1-1
if(aa(i3).eq.0)then
if(gam(i3,j1).gt.0)then
kk=kk+1
bb(kk)=i3
aa(i3)=jj
end if
end if
end do
do i3=j1+1,n
if(aa(i3).eq.0)then
if(gam(j1,i3).gt.0)then
kk=kk+1
bb(kk)=i3
aa(i3)=jj
end if
end if
end do
if(ii.lt.kk)then
if(kk.lt.n)then
ii=ii+1
go to 35
end if
end if
end do d03
if(kk.ne.n)then
qerrmsg(1:srec)='qumvi_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(jj.gt.0)then
cc(1:jj)=0
end if
do i2=1,rho(-1)
cc(aa(i2))=cc(aa(i2))+1
end do
do i2=1,jj
if(cc(i2).eq.1)then
go to 50
end if
end do
cycle d02
50 continue
j0=0
do i2=1,jj
bb(i2)=cc(i2)
if(cc(i2).eq.0)then
j0=j0+1
end if
end do
do i2=rhop1,n
if(i2.ne.i1)then
bb(aa(i2))=bb(aa(i2))+1
end if
end do
d04: do i2=1,jj
if(cc(i2).eq.1)then
j1=bb(i2)
j2=gam(i1,i1)
j3=j0
if(j1.eq.1)then
if(j2.gt.1)then
j2=j2-2
else if(j0.gt.0)then
i4=0
do i3=1,jj
if(cc(i3).eq.0)then
if(i4.eq.0)then
i4=i3
else if(bb(i3).lt.bb(i4))then
i4=i3
end if
end if
end do
j3=j3-1
j1=j1+bb(i4)
else
cycle d04
end if
end if
if(0.lt.j2+j3)then
go to 80
else if(j1+2.lt.n)then
go to 80
end if
end if
end do d04
end do d02
go to 99
80 continue
situ=-1
99 continue
return
end subroutine qumvi
integer(kind=c_int_least32_t) function qbprod(im,in)
use,non_intrinsic::qbounds
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::in
integer(kind=c_int_least32_t),intent(inout)::im
integer(kind=c_int_least32_t)::j1,j2,jm,jn
qbprod=0
jm=abs(im)
jn=abs(in)
if(jm.lt.jn)then
j1=jm
j2=jn
else
j1=jn
j2=jm
end if
if(j2.le.zbo%iref)then
serrt=qerrty%ok
else if(j1.le.zbo%iref)then
if(zbo%irefl/j2.ge.j1)then
serrt=qerrty%ok
else
serrt=qerrty%q
end if
else
serrt=qerrty%q
end if
if(serrt.eq.qerrty%ok)then
qbprod=im*in
else
qbprod=0
qerrt(0)=serrt
call qiomsg(21,0,0,0)
Q_ERRT
end if
99 continue
return
end function qbprod
subroutine qdkar(im,iw)
use,non_intrinsic::qaski
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::im
integer(kind=c_int_least32_t),intent(out)::iw
integer(kind=c_int_least32_t), external::qwztos
integer(kind=c_int_least32_t)::j1,j2,m1,m2
m1=abs(im)
if(m1.lt.10)then
iw=1
if(im.lt.0)then
zstr(1:1)=achar(aminus)
iw=2
end if
zstr(iw:iw)=achar(azero+int(m1))
go to 99
end if
iw=qwztos(m1)
Q_ERRT
serrt=qerrty%ok
if(iw.ge.zbo%wirefl-1)then
if(m1.gt.zbo%irefl)then
serrt=qerrty%q
end if
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(21,0,0,0)
Q_ERRT
end if
j1=1
if(im.lt.0)then
zstr(1:1)=achar(aminus)
iw=iw+1
j1=j1+1
end if
j2=iw
do while(m1.gt.9)
m2=m1/10
zstr(j2:j2)=achar(azero+int(m1-10*m2))
m1=m2
j2=j2-1
end do
if(j1.ne.j2)then
qerrmsg(1:srec)='qdkar_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
zstr(j2:j2)=achar(azero+int(m1))
99 continue
return
end subroutine qdkar
subroutine qxdkar(jn,jw)
use,non_intrinsic::qaski
use,non_intrinsic::qintr
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jn
integer(kind=c_int_least32_t),intent(out)::jw
integer(kind=c_int_least32_t)::i1,j1,j2,m1,m2
m1=abs(jn)
if(m1.le.zbo%iref)then
do i1=1,zbo%wiref
if(m1.lt.stib(ptenp(0)+i1))then
j1=i1
exit
end if
end do
else if(m1.le.zbo%irefl)then
j1=zbo%wirefl
do i1=zbo%wiref,zbo%spten
if(m1.lt.stib(ptenp(0)+i1))then
j1=i1
exit
end if
end do
else
if(qerrt(0).le.qerrty%ale)then
qerrt(0)=qerrty%q
call qiomsg(21,0,0,0)
Q_ERRT
end if
end if
jw=1
if(jn.lt.0)then
jw=jw+1
zstr(1:1)=achar(aminus)
end if
if(j1+jw.ge.len(zstr))then
if(qerrt(0).le.qerrty%ale)then
qerrt(0)=qerrty%q
call qiomsg(21,0,0,0)
Q_ERRT
end if
end if
j1=j1-1
do while(j1.gt.0)
j2=stib(ptenp(0)+j1)
m2=m1/j2
zstr(jw:jw)=achar(azero+int(m2))
m1=m1-m2*j2
j1=j1-1
jw=jw+1
end do
zstr(jw:jw)=achar(azero+int(m1))
zstr(jw+1:jw+1)=achar(anull)
99 continue
return
end subroutine qxdkar
subroutine qsdiag(ii,jj)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qmix
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ii,jj
integer(kind=c_int_least32_t)::i1,i2,j1,j3,j4,xp,xl
serrt=qerrty%ok
if((ii.le.0).or.&
(ii.gt.dcoty%ubo))then
qerrmsg(1:srec)='qsdiag_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
xp=qcop(ii)
xl=qcol(ii)
if(((xl.le.0).and.(jj.eq.0)).or.&
(xl.gt.zbo%wirefh))then
qerrmsg(1:srec)='qsdiag_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(jj.eq.0)then
do i1=xp+xl,xp+1,-1
j1=iachar(stcb(i1:i1))
if(int(j1).lt.anine)then
stcb(i1:i1)=achar(int(j1)+1)
exit
else
stcb(i1:i1)=achar(azero)
end if
end do
j1=xp+1
if(iachar(stcb(j1:j1)).eq.azero)then
stcb(j1:j1)=achar(azero+1)
xl=xl+1
stcb(xp+xl:xp+xl)=achar(azero)
end if
else if(jj.eq.-1)then
j1=xp+1
stcb(j1:j1)=achar(azero)
j1=j1+1
stcb(j1:j1+zbo%wirefh)=achar(anull)
xl=1
else
qerrmsg(1:srec)='qsdiag_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(xl.ge.zbo%wirefh)then
if(xl.gt.zbo%wirefh)then
qerrmsg(1:srec)='qsdiag_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
else if(xl.eq.zbo%wirefh)then
i2=stib(slhp(0)+inty%h)-1
do i1=xp+1,xp+xl
j3=iachar(stcb(i1:i1))
i2=i2+1
j4=iachar(stcb(i2:i2))
if(j3.gt.j4)then
serrt=qerrty%q
exit
else if(j3.lt.j4)then
exit
end if
end do
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(21,0,0,0)
Q_ERRT
end if
end if
end if
qcol(ii)=xl
99 continue
return
end subroutine qsdiag
integer(kind=c_int_least32_t) function qilsd(s,j1,j2)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::j1,j2
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::i1,xj1
qilsd=0
if(j1.le.0)then
qilsd=1
else if(j1.gt.j2)then
qilsd=1
else if(j2-j1.gt.zbo%wirefh-1)then
qilsd=1
end if
if(qilsd.ne.0)then
go to 80
end if
qilsd=iachar(s(j1:j1))
if((qilsd.eq.aplus).or.&
(qilsd.eq.aminus))then
xj1=j1+1
else
xj1=j1
end if
qilsd=j2
do i1=xj1,j2
if(iachar(s(i1:i1)).ne.azero)then
qilsd=i1
exit
end if
end do
go to 99
80 continue
qerrmsg(1:srec)='qilsd_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
99 continue
return
end function qilsd
subroutine qkbp(s,j1,j2,j3,k1,k2,k3)
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t),intent(in)::j1,j2,j3
integer(kind=c_int_least32_t),intent(out)::k1,k2,k3
type(qqll),pointer::qllp
integer(kind=c_int_least32_t)::i1,i2,j4,jl
integer(kind=c_int_least32_t)::q1,q2,qp2
k1=0
k2=nap
k3=0
serrt=qerrty%ok
if(j1.le.0)then
serrt=qerrty%q
else if(j2.le.0)then
serrt=qerrty%q
else if(j3.eq.0)then
serrt=qerrty%q
else
jl=(j2-j1)+1
if(jl.le.0)then
serrt=qerrty%q
end if
end if
j4=abs(j3)
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qkbp_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
d01: do i1=1,mll0
qllp=>qll(i1)
if(qllp%n.eq.0)then
cycle
else if(j3.gt.0)then
if(i1.ne.j3)then
cycle
end if
else
if(qllp%kl.ne.j4)then
cycle
end if
end if
q1=qllp%p1
qp2=qllp%p2
do i2=1,qllp%n
if(q1.eq.qp2)then
qerrmsg(1:srec)='qkbp_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
q1=stib(q1)
if(stib(q1+2).eq.jl)then
q2=stib(q1+1)
if(s(j1:j2).eq.s(q2:q2+(jl-1)))then
k1=i1
k2=q1
k3=i2
exit d01
end if
end if
end do
end do d01
99 continue
return
end subroutine qkbp
subroutine qvsf
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::i1,i2,i3,j1,j2,j3,j4,j5,j6,ii,p0,p1
integer(kind=c_int_least32_t)::atyp,styp
atyp=opety%psum
ii=stib(tftic(0)+atyp)
j3=0
do i1=stib(tfta(0)+ii),stib(tftb(0)+ii)
i2=stib(tf2(0)+i1)
styp=stib(tftyp(0)+i2)
if(j3.eq.0)then
if((abs(styp).ne.atyp).or.&
(pmkd(0).eq.nap).or.&
(pmkt(0).eq.nap).or.&
(pmkvmi(0).eq.nap).or.&
(pmkvma(0).eq.nap).or.&
(pmkzp(0).eq.nap))then
qerrmsg(1:srec)='qvsf_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
j3=stib(stib(tfo(0)+i2)+1)
if((stib(pmkd(0)+j3).ne.1).or.&
(stib(pmkt(0)+j3).ne.futyp%z).or.&
(stib(pmkvmi(0)+j3).eq.nap).or.&
(stib(pmkvma(0)+j3).eq.nap).or.&
(stib(pmkzp(0)+j3).eq.nap))then
qerrmsg(1:srec)='qvsf_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(styp.lt.0)then
cycle
end if
j1=stib(pmkvmi(0)+j3)
j2=stib(pmkvma(0)+j3)
if(styp.gt.0)then
if(j1.ge.0)then
if(j1.gt.stib(tfb(0)+i2))then
jflag(jflaty%noge)=1
end if
else if(j2.le.0)then
if(j2.lt.stib(tfa(0)+i2))then
jflag(jflaty%noge)=1
end if
end if
end if
if(psfi(0)==nap)then
psfi(0)=stibs(1)
call qaoib(nphi+1)
Q_ERRT
stib(psfi(0)+1:stibs(1)-1)=0
stib(stibs(1))=eoa
end if
j4=stib(pmkzp(0)+j3)
j1=0
j2=0
do i3=1,nphi
j5=stib(j4+i3)
if(j5.gt.0)then
j2=j2+1
else if(j5.lt.0)then
j1=j1+1
end if
end do
if((j1.gt.0).and.&
(j2.gt.0))then
cycle
else if(j1.eq.0)then
j5=stib(tfb(0)+i2)
do i3=1,nphi
if(stib(j4+i3).gt.j5)then
jflag(jflaty%pexc)=1
stib(psfi(0)+i3)=1
end if
end do
else if(j2.eq.0)then
j5=stib(tfa(0)+i2)
do i3=1,nphi
if(stib(j4+i3).lt.j5)then
jflag(jflaty%pexc)=1
stib(psfi(0)+i3)=1
end if
end do
end if
end do
if(jflag(jflaty%pexc).eq.0)then
if(psfi(0).ne.nap)then
call qaoib(-(nphi+1))
Q_ERRT
psfi(0)=nap
end if
else
ii=0
do i1=1,nphi
if(stib(tpc(0)+i1).ne.phity%ext)then
if(stib(psfi(0)+i1).eq.0)then
ii=ii+1
exit
end if
end if
end do
if(ii.eq.0)then
jflag(jflaty%noge)=1
end if
end if
atyp=opety%vsum
ii=stib(tftic(0)+atyp)
j3=0
do i1=stib(tfta(0)+ii),stib(tftb(0)+ii)
i2=stib(tf2(0)+i1)
styp=stib(tftyp(0)+i2)
if(j3.eq.0)then
if((abs(styp).ne.atyp).or.&
(vmks(0).eq.nap).or.&
(vmkt(0).eq.nap).or.&
(vmkmio(0).eq.nap).or.&
(vmkmao(0).eq.nap).or.&
(vmkzp(0).eq.nap))then
qerrmsg(1:srec)='qvsf_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
j3=stib(stib(tfo(0)+i2)+1)
if((stib(vmks(0)+j3).eq.0).or.&
(stib(vmkt(0)+j3).ne.futyp%z).or.&
(stib(vmkmio(0)+j3).eq.nap).or.&
(stib(vmkmao(0)+j3).eq.nap).or.&
(stib(vmkzp(0)+j3).eq.nap))then
qerrmsg(1:srec)='qvsf_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(styp.lt.0)then
cycle
else
j1=0
j2=0
j6=0
do i3=nrho,mrho,-1
if(stib(nivd(0)+i3).gt.0)then
j4=stib(stib(vmkmio(0)+j3)+i3)
j5=stib(stib(vmkmao(0)+j3)+i3)
if(j6.eq.0)then
j6=1
j1=j4
j2=j5
else if(j1.gt.j4)then
j1=j4
else if(j2.lt.j5)then
j2=j5
end if
end if
end do
if(j1.ge.0)then
if(j1.gt.stib(tfb(0)+i2))then
jflag(jflaty%noga)=1
end if
else if(j2.le.0)then
if(j2.lt.stib(tfa(0)+i2))then
jflag(jflaty%noga)=1
end if
end if
end if
if(jflag(jflaty%noga).ne.0)then
go to 99
end if
if(vsfi(0).eq.nap)then
vsfi(0)=stibs(1)
call qaoib(nvert+1)
Q_ERRT
stib(vsfi(0)+1:stibs(1)-1)=0
stib(stibs(1))=eoa
end if
j4=stib(vmkzp(0)+j3)
j1=0
j2=0
do i3=1,nvert
j5=stib(j4+i3)
if(j5.gt.0)then
j2=j2+1
else if(j5.lt.0)then
j1=j1+1
end if
end do
if((j1.gt.0).and.&
(j2.gt.0))then
cycle
else if(j1.eq.0)then
j5=stib(tfb(0)+i2)
do i3=1,nvert
if(stib(j4+i3).gt.j5)then
jflag(jflaty%vexc)=1
stib(vsfi(0)+i3)=1
end if
end do
else if(j2.eq.0)then
j5=stib(tfa(0)+i2)
do i3=1,nvert
if(stib(j4+i3).lt.j5)then
jflag(jflaty%vexc)=1
stib(vsfi(0)+i3)=1
end if
end do
end if
end do
if(jflag(jflaty%pexc).ne.0)then
if(vsfi(0).eq.nap)then
vsfi(0)=stibs(1)
call qaoib(nvert+1)
Q_ERRT
stib(vsfi(0)+1:stibs(1)-1)=0
stib(stibs(1))=eoa
end if
p0=stibs(1)
call qaoib(nphi+1)
Q_ERRT
stib(p0+1:stibs(1)-1)=0
stib(stibs(1))=eoa
do i2=1,nleg
j1=p0+stib(link(0)+stib(leg(0)+i2))
stib(j1)=stib(j1)+1
end do
p1=stibs(1)
call qaoib(nphi+1)
Q_ERRT
stib(p1+1:stibs(1)-1)=0
stib(stibs(1))=eoa
do i2=1,nvert
if(stib(vsfi(0)+i2).eq.0)then
j1=stib(vparto(0)+i2)
do i3=1,stib(vval(0)+i2)
j3=stib(j1+i3)
if(stib(psfi(0)+j3).ne.0)then
j2=p1+j3
stib(j2)=stib(j2)+1
if(stib(j2).gt.stib(p0+j3))then
stib(vsfi(0)+i2)=1
jflag(jflaty%vexc)=1
exit
end if
end if
end do
do i3=1,stib(vval(0)+i2)
stib(p1+stib(j1+i3))=0
end do
end if
end do
call qaoib(-2*(nphi+1))
Q_ERRT
end if
if(jflag(jflaty%vexc).eq.0)then
if(vsfi(0).ne.nap)then
call qaoib(-(nvert+1))
Q_ERRT
vsfi(0)=nap
end if
else
ii=nrho+1
nivdx(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(nivdx(0)+1:stibs(1)-1)=0
stib(stibs(1))=eoa
do i1=1,nvert
if(stib(vsfi(0)+i1).eq.0)then
p1=nivdx(0)+stib(vval(0)+i1)
stib(p1)=stib(p1)+1
end if
end do
ii=0
do i1=mrho,nrho
if(stib(nivdx(0)+i1).ne.0)then
ii=ii+1
exit
end if
end do
if(ii.eq.0)then
jflag(jflaty%noga)=1
end if
end if
if(jflag(jflaty%pexc).ne.0)then
if(nleg.gt.2)then
if(nleg.gt.nrho)then
jflag(jflaty%noga)=1
else if(nivdx(0).ne.nap)then
if(stib(nivdx(0)+nleg).eq.0)then
jflag(jflaty%noga)=1
end if
end if
end if
end if
99 continue
return
end subroutine qvsf
integer(kind=c_int_least32_t) function qstoz(s,j1,j2,jt)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::j1,j2,jt
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::i1,jj,js
qstoz=0
serrt=qerrty%ok
if(j1.le.0)then
serrt=qerrty%q
else if(j1.gt.j2)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
js=iachar(s(j1:j1))
if((js.eq.aplus).or.&
(js.eq.aminus))then
i1=j1+1
else
i1=j1
end if
10 continue
jj=iachar(s(i1:i1))
if(acf(jj).eq.chty%digit)then
if(jt.eq.inty%s)then
if(qstoz-zbo%iref10.gt.0)then
serrt=qerrty%q
end if
else if(jt.eq.inty%l)then
if(qstoz-zbo%irefl10.gt.0)then
serrt=qerrty%q
end if
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(21,0,0,0)
Q_ERRT
end if
qstoz=10*qstoz+int(jj-azero,c_int_least32_t)
if(i1.lt.j2)then
i1=i1+1
go to 10
end if
if(jt.eq.inty%s)then
if(qstoz-zbo%iref.gt.0)then
serrt=qerrty%q
end if
else if(jt.eq.inty%l)then
if(qstoz-zbo%irefl.gt.0)then
serrt=qerrty%q
end if
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(21,0,0,0)
Q_ERRT
end if
if(js.eq.aminus)then
qstoz=-qstoz
end if
go to 99
end if
80 continue
qerrmsg(1:srec)='qstoz_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
99 continue
return
end function qstoz
integer(kind=c_int_least32_t) function qsigz(s,ia,ib)
use,non_intrinsic::qaski
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::i1,ii,jj,ja
qsigz=0
if(ia.le.0)then
go to 80
end if
jj=iachar(s(ia:ia))
if(jj.eq.aplus)then
ii=1
else if(jj.eq.aminus)then
ii=-1
else
ii=0
end if
ja=ia+abs(ii)
if(ja.gt.ib)then
go to 80
end if
do i1=ja,ib
jj=iachar(s(i1:i1))
if(acf(jj).ne.chty%digit)then
go to 80
else if(qsigz.eq.0)then
if(int(jj).ne.azero)then
if(ii.lt.0)then
qsigz=-1
else
qsigz=1
end if
end if
end if
end do
go to 99
80 continue
qerrmsg(1:srec)='qsigz_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
99 continue
return
end function qsigz
integer(kind=c_int_least32_t) function qwztos(nn)
use,non_intrinsic::qbounds
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::nn
integer(kind=c_int_least32_t)::mm,i1,j1
qwztos=0
if(nn.ge.0)then
if(nn.le.zbo%irefl)then
mm=nn
else
qwztos=-1
end if
else
if(nn.ge.-zbo%irefl)then
mm=-nn
qwztos=1
else
qwztos=-1
end if
end if
if(qwztos.lt.0)then
if(qerrt(0).le.qerrty%ale)then
qerrt(0)=qerrty%q
call qiomsg(21,0,0,0)
Q_ERRT
end if
end if
j1=ptenp(0)
do i1=1,zbo%spten
j1=j1+1
if(mm.lt.stib(j1))then
qwztos=qwztos+i1
go to 99
end if
end do
qwztos=qwztos+zbo%spten+1
99 continue
return
end function qwztos
subroutine qspak(s,ind,m,uc,nos)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t),intent(inout)::ind
integer(kind=c_int_least32_t),intent(in)::m,uc,nos
integer(kind=c_int_least32_t), external::qstoz
integer(kind=c_int_least32_t)::i1,i2,i3,j0,j1,j2,j3
integer(kind=c_int_least32_t)::ii,ij,inos,jj,k,kk,sl,sp
if((m.ne.0).and.&
(m.ne.1))then
go to 80
else if((nos.ne.0).and.&
(nos.ne.1))then
go to 80
else if((uc.ne.0).and.&
(uc.ne.1))then
go to 80
end if
inos=nos
i1=0
sl=1
ii=2*srec+1
do while(iachar(s(sl:sl)).ne.ascol)
if(sl.lt.ii)then
if(i1.eq.0)then
if(iachar(s(sl:sl)).eq.acomma)then
i1=sl
end if
end if
sl=sl+1
else
go to 80
end if
end do
if(i1.eq.0)then
i1=sl
end if
if(i1.lt.3)then
go to 80
else if(sl.lt.3)then
go to 80
else if(modulo(i1,2).eq.0)then
go to 80
end if
sp=stcbs(1)+1
i1=(i1-1)/2
call qaocb(i1+1)
Q_ERRT
ij=0
j2=-1
k=sp
do i2=1,i1
j2=j2+2
ii=iachar(s(j2:j2))
jj=iachar(s(j2+1:j2+1))
if((int(ii).lt.azero).or.&
(int(ii).gt.anine))then
go to 80
else if((int(jj).lt.azero).or.&
(int(jj).gt.anine))then
go to 80
end if
kk=10*ii+jj-496
if(uc.ne.0)then
if(kk.ge.abo(3))then
if(kk.le.abo(4))then
go to 80
end if
end if
end if
if(kk.ge.abo(5))then
if(kk.le.abo(6))then
ij=1
end if
end if
stcb(k:k)=achar(kk)
k=k+1
end do
stcb(k:k)=achar(anull)
if(uc.ne.0)then
if(ij.eq.0)then
go to 80
end if
end if
if(inos.ne.0)then
if(iachar(stcb(k-1:k-1)).ne.kpqs(4))then
inos=0
end if
end if
j0=stibs(1)
call qaoib(2)
Q_ERRT
stib(j0+1)=sp
stib(j0+2)=i1
if(m.ne.0)then
if((nos.ne.0).or.&
(uc.ne.0))then
go to 80
end if
go to 99
end if
j2=2*i1+1
j1=j2+1
do while(j2.lt.sl)
j2=j2+1
j3=iachar(s(j2:j2))
if((j3.eq.acomma).or.&
(j3.eq.ascol))then
j2=j2-1
if(j2.lt.j1)then
go to 80
end if
call qaoib(1)
Q_ERRT
stib(stibs(1))=qstoz(s,j1,j2,inty%s)
Q_ERRT
j2=j2+1
j1=j2+1
end if
end do
ind=ind+1
if(uc.ne.0)then
ii=stcbs(1)
call qaocb(i1+1)
Q_ERRT
i3=ii+1
do i2=ii-i1,ii-1
j2=iachar(stcb(i2:i2))
if((j2.ge.abo(5)).and.&
(j2.le.abo(6)))then
j2=j2+abo(0)
end if
stcb(i3:i3)=achar(j2)
i3=i3+1
end do
stcb(i3:i3)=achar(anull)
j1=stibs(1)
jj=j1-j0
if(jj.lt.2)then
go to 80
end if
call qaoib(jj)
Q_ERRT
ii=j1+1
stib(ii)=stib(ii-jj)+i1+1
do i2=2,jj
ii=ii+1
stib(ii)=stib(ii-jj)
end do
ind=ind+1
end if
if(inos.ne.0)then
j1=stibs(1)
jj=j1-j0
if(jj.lt.4)then
go to 80
end if
call qaoib(jj)
Q_ERRT
ii=j1
do i2=1,jj
ii=ii+1
stib(ii)=stib(ii-jj)
end do
ii=j1+2
stib(ii)=stib(ii)-1
ind=ind+1
if(uc.ne.0)then
ii=ii+(jj/2)
stib(ii)=stib(ii)-1
ind=ind+1
end if
end if
go to 99
80 continue
qerrmsg(1:srec)='qspak_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
99 continue
return
end subroutine qspak
subroutine qspok(s,aa,m,ind,uc,nos)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::dspok0=3
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t),intent(in)::m,uc,nos
integer(kind=c_int_least32_t),intent(in)::aa(m)
integer(kind=c_int_least32_t),intent(inout)::ind
integer(kind=c_int_least32_t), external::qstoz
integer(kind=c_int_least32_t)::i1,j0,j1,j2,j3
integer(kind=c_int_least32_t)::ii,ij,inos,jj,k,kk,sl,sp
if((m.lt.0).or.&
(m.gt.dspok0))then
go to 80
else if((nos.ne.0).and.&
(nos.ne.1))then
go to 80
else if((uc.ne.0).and.&
(uc.ne.1))then
go to 80
end if
inos=nos
j1=0
sl=1
ii=2*srec+2
do while(iachar(s(sl:sl)).ne.ascol)
if(sl.lt.ii)then
if(j1.eq.0)then
if(iachar(s(sl:sl)).eq.acomma)then
j1=sl
end if
end if
sl=sl+1
else
go to 80
end if
end do
if(j1.eq.0)then
j1=sl
end if
if(j1.lt.3)then
go to 80
else if(sl.lt.3)then
go to 80
else if(modulo(j1,2).eq.0)then
go to 80
end if
sp=stcbs(1)+1
sl=(j1-1)/2
call qaocb(sl+1)
Q_ERRT
j2=-1
k=sp
ij=0
do i1=1,sl
j2=j2+2
ii=iachar(s(j2:j2))
jj=iachar(s(j2+1:j2+1))
if((int(ii).lt.azero).or.&
(int(ii).gt.anine))then
go to 80
else if((int(jj).lt.azero).or.&
(int(jj).gt.anine))then
go to 80
end if
kk=10*ii+jj-496
if(uc.ne.0)then
if(kk.ge.abo(3))then
if(kk.le.abo(4))then
go to 80
end if
end if
end if
if(kk.ge.abo(5))then
if(kk.le.abo(6))then
ij=1
end if
end if
stcb(k:k)=achar(kk)
k=k+1
end do
if(ij.eq.0)then
if(uc.ne.0)then
go to 80
end if
end if
stcb(k:k)=achar(anull)
if(inos.ne.0)then
if(iachar(stcb(k-1:k-1)).ne.kpqs(4))then
inos=0
end if
end if
j0=stibs(1)+1
call qaoib(m+2)
Q_ERRT
stib(j0)=sp
stib(j0+1)=sl
if(m.eq.0)then
if(abs(nos)+abs(uc).eq.0)then
go to 99
else
go to 80
end if
end if
j0=j0+1
stib(j0+1:j0+m)=aa(1:m)
ind=ind+1
if(inos.ne.0)then
j2=stcbs(1)+1
call qaocb(sl)
Q_ERRT
stcb(j2:j2+(sl-1))=stcb(sp:sp+(sl-2))//achar(anull)
j1=stibs(1)+1
call qaoib(m+2)
Q_ERRT
stib(j1)=j2
j1=j1+1
stib(j1)=sl-1
stib(j1+1:j1+m)=aa(1:m)
ind=ind+1
end if
if(uc.ne.0)then
j2=stcbs(1)
kk=j2
call qaocb(sl+1)
Q_ERRT
do i1=sp,sp+(sl-1)
j3=iachar(stcb(i1:i1))
if((j3.ge.abo(5)).and.&
(j3.le.abo(6)))then
j3=j3+abo(0)
end if
j2=j2+1
stcb(j2:j2)=achar(j3)
end do
stcb(stcbs(1):stcbs(1))=achar(anull)
j1=stibs(1)+1
call qaoib(m+2)
Q_ERRT
stib(j1)=kk+1
j1=j1+1
stib(j1)=sl
stib(j1+1:j1+m)=aa(1:m)
ind=ind+1
end if
if((uc.ne.0).and.&
(inos.ne.0))then
j2=stcbs(1)+1
call qaocb(sl)
Q_ERRT
stcb(j2:stcbs(1))=stcb(kk+1:kk+(sl-1))//achar(anull)
j1=stibs(1)+1
call qaoib(m+2)
Q_ERRT
stib(j1)=j2
j1=j1+1
stib(j1)=sl-1
stib(j1+1:j1+m)=aa(1:m)
ind=ind+1
end if
go to 99
80 continue
qerrmsg(1:srec)='qspok_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
99 continue
return
end subroutine qspok
integer(kind=c_int_least32_t) function qstds(s,ia,ib,iw)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib,iw
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::i1,j1,ii,jj,kk,ll,mm,itl,sc,sf
qstds=0
serrt=qerrty%ok
if(ia.le.0)then
serrt=qerrty%q
else if(ia.ge.ib)then
serrt=qerrty%q
else if(iachar(s(ia:ia)).ne.asq)then
serrt=qerrty%q
else if(iachar(s(ib:ib)).ne.asq)then
serrt=qerrty%q
else if(iw.lt.0)then
serrt=qerrty%q
else if(iw.gt.2)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qstds=-1
go to 99
end if
sc=0
sf=0
itl=1
ii=0
ll=0
mm=0
do i1=ia,ib
jj=iachar(s(i1:i1))
if(jj.eq.asq)then
ii=ii+1
mm=1-mm
ll=0
if(ii.gt.1)then
kk=mm
else
kk=0
end if
else if(jj.eq.anull)then
if(mm.ne.0)then
go to 70
else if(ll.eq.1)then
go to 70
end if
sf=sf+1
ll=1
if(ii.gt.0)then
ii=0
sc=sc+1
end if
kk=0
else if(jj.eq.aspc)then
if(ii.gt.0)then
ii=0
if(mm.eq.0)then
sc=sc+1
end if
end if
kk=mm
else if((jj.lt.abo(1)).or.&
(jj.gt.abo(2)))then
go to 70
else
if(mm.ne.1)then
go to 70
end if
ii=0
kk=1
end if
if(kk.ne.0)then
if(iw.eq.2)then
if(jj.ne.aspc)then
itl=0
end if
end if
if((iw.eq.1).or.&
((iw.eq.2).and.(itl.eq.0)))then
qstds=qstds+1
call qvaocb(qstds)
Q_ERRT
j1=stcbs(1)+qstds
stcb(j1:j1)=achar(jj)
end if
end if
end do
if(mm.ne.0)then
go to 70
end if
if(iachar(s(ib:ib)).eq.asq)then
sc=sc+1
end if
if(iw.eq.2)then
if(qstds.gt.1)then
do i1=stcbs(1)+qstds,stcbs(1)+1,-1
if(iachar(stcb(i1:i1)).ne.aspc)then
exit
end if
qstds=qstds-1
end do
end if
end if
70 continue
if(qstds.gt.0)then
call qaocb(qstds+1)
Q_ERRT
j1=stcbs(1)+qstds+1
stcb(j1:j1)=achar(anull)
end if
99 continue
return
end function qstds
subroutine qmstr0(s,ia,ib,pp,pl,ap,ind)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib,pp,pl,ap
integer(kind=c_int_least32_t),intent(inout)::ind
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::ii,jj,kk,iind,ls
if(ind.ne.0)then
if(ind.ne.1)then
qerrmsg(1:srec)='qmstr0_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
iind=ind
if(pp.eq.nap)then
ind=-1
else if(pl.eq.nap)then
ind=-1
else
ind=0
ls=ib-ia+1
kk=1
ii=stib(pl+1)
do while(ii.ne.eoa)
if(ii.eq.ls)then
jj=stib(pp+kk)
if(stcb(jj:jj-1+ls).eq.s(ia:ib))then
ind=kk
if(iind.eq.0)then
exit
end if
end if
end if
kk=kk+1
ii=stib(pl+kk)
end do
if(ap.ne.nap)then
if(ind.gt.0)then
ind=stib(ap+ind)
end if
end if
end if
if(ind.lt.0)then
qerrmsg(1:srec)='qmstr0_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
99 continue
return
end subroutine qmstr0
subroutine qmstr1(s,ia,ib,pp,kp,kl,ind,qq)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib,pp,kp,kl
integer(kind=c_int_least32_t),intent(out)::ind,qq
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::jj,kk,ls,p1
qq=nap
if(pp.eq.nap)then
ind=-1
else if(kp.le.0)then
ind=-1
else if(kl.le.0)then
ind=-1
else
ind=0
ls=ib-(ia-1)
kk=0
p1=stib(pp)
do while(p1.ne.eoa)
kk=kk+1
if(stib(p1+kl).eq.ls)then
jj=stib(p1+kp)
if(stcb(jj:jj-1+ls).eq.s(ia:ib))then
ind=kk
qq=p1
exit
end if
end if
p1=stib(p1)
end do
end if
if(ind.lt.0)then
qerrmsg(1:srec)='qmstr1_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
99 continue
return
end subroutine qmstr1
integer(kind=c_int_least32_t) function qstdpa(s,ia,ib)
use,non_intrinsic::qaski
use,non_intrinsic::qfiles
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::ic,i1,i2,j1,j2,j3
qstdpa=0
if((ia.le.0).or.&
(ia.gt.ib))then
qerrmsg(1:srec)='qstdpa_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
serrt=qerrty%ok
j2=ia-1
ic=ib+1
do i1=ia,ic
if(i1.lt.ic)then
j1=iachar(s(i1:i1))
else
j1=p_sep
end if
if(j1.eq.p_sep)then
if(p_sep.eq.aslash)then
if(j2.eq.i1-1)then
j2=i1
cycle
else if(j2.eq.i1-2)then
if(iachar(s(j2+1:j2+1)).eq.adot)then
j2=i1
cycle
end if
else if(j2.eq.i1-3)then
if(s(j2+1:j2+2).eq.'..')then
j2=i1
cycle
end if
end if
end if
if((acf(iachar(s(j2+1:j2+1))).le.0).or.&
(acf(iachar(s(i1-1:i1-1))).le.0))then
serrt=qerrty%inp
exit
end if
j3=0
do i2=j2+2,i1-2
j1=iachar(s(i2:i2))
if(acf(j1).gt.0)then
j3=0
else
if(j3.ne.0)then
serrt=qerrty%inp
exit
end if
if(j1.ne.adot)then
if(j1.ne.ausc)then
if(j1.ne.aminus)then
serrt=qerrty%inp
exit
end if
end if
end if
j3=1
end if
end do
j2=i1
end if
end do
if(serrt.eq.qerrty%ok)then
qstdpa=1
end if
99 continue
return
end function qstdpa
integer(kind=c_int_least32_t) function qstdw(s,ia,ib)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer,only:stcbas
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::i1,j1
qstdw=0
if(ia.le.0)then
serrt=qerrty%q
else if(stcbas(1).lt.ib)then
serrt=qerrty%q
else if(ia.gt.ib)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qstdw_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
j1=acf(iachar(s(ia:ia)))
if((j1.eq.chty%ucase).or.&
(j1.eq.chty%lcase))then
qstdw=1
do i1=ia+1,ib
if(acf(iachar(s(i1:i1))).lt.0)then
qstdw=0
exit
end if
end do
end if
99 continue
return
end function qstdw
integer(kind=c_int_least32_t) function qstdz(s,ia,ib,it)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib,it
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::i1,i2,j1,j2,j3,j4,jj,ll
qstdz=0
serrt=qerrty%ok
if(ia.le.0)then
serrt=qerrty%q
else if(ib.lt.ia)then
serrt=qerrty%q
else if(stcbas(1).lt.ib)then
serrt=qerrty%q
else if(abs(it-2).gt.1)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qstdz_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
j1=ia
j2=ib
if(j1.le.j2)then
jj=iachar(s(j1:j1))
if(jj.eq.aplus)then
j1=j1+1
else if(jj.eq.aminus)then
j1=j1+1
end if
do while((j1.lt.j2).and.(iachar(s(j1:j1)).eq.azero))
j1=j1+1
end do
ll=j2-(j1-1)
if(it.eq.inty%s)then
jj=zbo%wiref
else if(it.eq.inty%l)then
jj=zbo%wirefl
else if(it.eq.inty%h)then
jj=zbo%wirefh
end if
if(ll.le.jj)then
do i1=j1,j2
if(acf(iachar(s(i1:i1))).ne.chty%digit)then
go to 99
end if
end do
if(ll.eq.jj)then
i2=stib(slhp(0)+it)-1
do i1=j1,j2
j3=iachar(s(i1:i1))
i2=i2+1
j4=iachar(stcb(i2:i2))
if(j3.gt.j4)then
go to 99
else if(j3.lt.j4)then
exit
end if
end do
end if
qstdz=1
end if
end if
99 continue
return
end function qstdz
subroutine qnows(j1,j2,k1)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::j1,j2,k1
integer(kind=c_int_least32_t)::i1,j3,j4
serrt=qerrty%ok
if(j1.le.0)then
serrt=qerrty%q
else if(k1.lt.0)then
serrt=qerrty%q
else if(j1.ge.j2)then
serrt=qerrty%q
else if(j2.gt.stcbas(1))then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qnows_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
j3=0
do i1=j1+1,j2-1
if(iachar(stcb(i1:i1)).eq.aspc)then
j3=j3+1
end if
end do
if(j3.gt.0)then
j4=j2-j1-(j3-1)
j3=stcbs(1)
call qaocb(j4)
Q_ERRT
j4=j3
do i1=j1,j2
if(iachar(stcb(i1:i1)).ne.aspc)then
j4=j4+1
stcb(j4:j4)=stcb(i1:i1)
end if
end do
if(k1.gt.0)then
stjb(k1)=j3+1
stjb(k1+1)=stcbs(1)
end if
end if
99 continue
return
end subroutine qnows
integer(kind=c_int_least32_t) function qstdq(s,ia,ib,it)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qbounds
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstdz,qstoz
integer(kind=c_int_least32_t),intent(in)::ia,ib,it
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least64_t)::jh,kh
integer(kind=c_int_least32_t)::i1,ii,jj,kk,j1,k1,jt,xsla
qstdq=1
serrt=qerrty%ok
if(ia.le.0)then
serrt=qerrty%q
else if(ib.lt.ia)then
serrt=qerrty%q
else if(stcbas(1).lt.ib)then
serrt=qerrty%q
else if(abs(it-2).gt.1)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qstdq_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
jt=it
xsla=0
do i1=ia,ib
if(iachar(s(i1:i1)).eq.aslash)then
xsla=xsla+1
if(i1.eq.ib)then
qstdq=0
else if(i1.eq.ia)then
qstdq=0
exit
else if(xsla.gt.1)then
qstdq=0
exit
else
ii=i1
end if
end if
end do
if(qstdq.ne.0)then
if(xsla.eq.0)then
qstdq=qstdz(s,ia,ib,jt)
Q_ERRT
else
jj=iachar(s(ii+1:ii+1))
if((jj.eq.aplus).or.&
(jj.eq.aminus))then
qstdq=0
else
qstdq=qstdz(s,ia,ii-1,jt)
Q_ERRT
if(qstdq.ne.0)then
jj=qstoz(s,ia,ii-1,jt)
Q_ERRT
qstdq=qstdz(s,ii+1,ib,jt)
Q_ERRT
if(qstdq.ne.0)then
kk=qstoz(s,ii+1,ib,jt)
Q_ERRT
if(kk.eq.0)then
qstdq=0
else if(jj.eq.0)then
qstdq=1
else if(jt.eq.inty%s)then
if(jj*kk.gt.zbo%iref)then
qstdq=0
end if
else
if(jt.eq.inty%l)then
j1=min(jj,kk)
k1=max(jj,kk)
if(j1.gt.zbo%iref)then
qstdq=0
else if(j1.gt.zbo%irefl/k1)then
qstdq=0
end if
else if(jt.eq.inty%h)then
jh=int(min(jj,kk),c_int_least64_t)
kh=int(max(jj,kk),c_int_least64_t)
if(jh.gt.zbo%irefh/kh)then
qstdq=0
end if
end if
end if
end if
end if
end if
end if
end if
99 continue
return
end function qstdq
integer(kind=c_int_least32_t) function qstdfty(s,ia,ib)
use,non_intrinsic::qbounds
use,non_intrinsic::qimodel
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstdz,qstdq,qstdw,qstds
integer(kind=c_int_least32_t),intent(inout)::ia,ib
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::ii
qstdfty=0
if(ia.gt.ib)then
serrt=qerrty%q
else
ii=qstdz(s,ia,ib,inty%s)
Q_ERRT
if(ii.gt.0)then
qstdfty=futyp%z
else
ii=qstdq(s,ia,ib,inty%s)
Q_ERRT
if(ii.gt.0)then
qstdfty=futyp%q
else
ii=qstdw(s,ia,ib)
Q_ERRT
if(ii.gt.0)then
qstdfty=futyp%id
else
ii=1
if(ii.gt.0)then
qstdfty=futyp%sqs
else
serrt=qerrty%q
end if
end if
end if
end if
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=qerrty%q
qerrmsg(1:srec)='qstdfty_1'//achar(anull)
call qmput(0,0,0)
Q_ERRT
end if
99 continue
return
end function qstdfty
subroutine qompac
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qsty
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
#ifdef Q_API
use,non_intrinsic::q_api
#endif
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qbprod
integer(kind=c_int_least32_t)::i,i1,i2,ia,ii,ij,ikm,il,j,jj,jjj,jk,j1,j2,j3,j4,kk,kf
integer(kind=c_int_least32_t)::f0,f1,f2,elupt,lupi,lupj,lupt,kma
integer(kind=c_int_least32_t)::lupk,luptt
integer(kind=c_int_least32_t)::ig,igc,igk,igut,ip,stwbp,stwbq,stwbt,stwbu
integer(kind=c_int_least32_t)::lupti(0:maxtak)
ig=iogp(2)
if(ig.ge.iogp(3))then
go to 80
end if
f0=0
01 continue
f0=f0+1
if(f0.gt.nfiles)then
go to 99
else if(filt(f0).ne.qfty%otyp)then
if(filt(f0).ne.qfty%ptyp)then
go to 01
end if
end if
if((qxmod.eq.qmod%api).or.&
(filp(f0).ne.nap))then
ig=ig+2
else
ig=ig+stib(ig+1)
go to 01
end if
f1=filo(f0)
f2=film(f0)
serrt=qerrty%ok
if(f1.lt.1)then
serrt=qerrty%q
else if(f1.gt.nsfiles)then
serrt=qerrty%q
else if(stib(ig-2).ne.eosf)then
serrt=qerrty%q
else if((filt(f0).ne.qfty%otyp).and.&
(filt(f0).ne.qfty%ptyp))then
serrt=qerrty%q
end if
if(f1.lt.nsfiles)then
if(stib(ig-2+stib(ig-1)).ne.eosf)then
serrt=qerrty%q
end if
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qompaq_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
#ifdef Q_API
if(qxmod.eq.qmod%api)then
stwbqf(f1)=stwbpf(f1)
if(obsel(f1).eq.qisgnl%n)then
call qpout(f0)
Q_ERRT
ig=(ig-1)+(stib(ig-1)-1)
go to 01
end if
end if
#endif
stwbp=stwbpf(f1)
stwbq=stwbqf(f1)
stwbu=stwbuf(f1)
stwbt=stwbp+swbuff0
lupti(0:maxtak)=0
kma=-1
lupt=0
10 continue
igk=stib(ig)
if(igk.gt.0)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(igk)
ig=ig+1
go to 10
end if
if(igk.gt.-3)then
igc=stib(ig+1)
if(igk.eq.-1)then
lupt=igc
if(lupt.gt.0)then
if(stib(ig+4).eq.0)then
if(lupt.eq.stylo%i)then
stib(ig+4)=inco
stib(ig+5)=0
lupti(0)=1
lupti(1)=lupt
else if(lupt.eq.stylo%o)then
stib(ig+4)=nleg
stib(ig+5)=inco
lupti(0)=1
lupti(1)=lupt
else if(lupt.eq.stylo%p)then
stib(ig+4)=nli-nleg
stib(ig+5)=0
lupti(0)=1
lupti(1)=lupt
else if(lupt.eq.stylo%v)then
stib(ig+4)=n-nleg
stib(ig+5)=0
lupti(0)=1
lupti(1)=lupt
else if(lupt.eq.stylo%r)then
stib(ig+4)=vdeg(nleg+lupi)
stib(ig+5)=0
if(lupti(0).ne.1)then
go to 80
end if
lupti(0)=2
lupti(2)=lupt
else if(lupt.eq.stylo%m)then
if(lupti(0).le.0)then
go to 80
else if(lupti(0).ge.maxtak)then
go to 80
end if
kf=0
lupti(0)=lupti(0)+1
lupti(lupti(0))=lupt
stib(ig+4)=nleg+nloop
stib(ig+5)=0
end if
end if
stib(ig+5)=stib(ig+5)+1
if(lupt.eq.stylo%m)then
stib(ig+5)=max(stib(ig+5),lupk+1)
end if
if(stib(ig+4).lt.stib(ig+5))then
stib(ig+4)=0
lupk=0
luptt=0
lupti(0)=lupti(0)-1
if(lupti(0).gt.0)then
lupt=lupti(lupti(0))
else
lupt=0
end if
ig=ig+1
else
if(lupt.eq.stylo%r)then
lupj=stib(ig+5)
else if(lupt.eq.stylo%m)then
lupk=stib(ig+5)
luptt=lupti(lupti(0)-1)
else
lupi=stib(ig+5)
lupj=0
lupk=0
end if
end if
else if(lupt.ne.stylo%end)then
go to 80
end if
else if(igk.eq.-2)then
if(igc.eq.22)then
if(jflag(jflaty%backmod).eq.0)then
if(kma.ge.0)then
stwbq=kma
kma=-1
end if
else if(stwbq.gt.stwbp)then
stwbq=stwbq-1
else
go to 80
end if
else
go to 80
end if
else
go to 80
end if
else if(igk.gt.-5)then
igc=stib(ig+1)
if(igk.eq.-3)then
if(igc.lt.67)then
if(igc.eq.61)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
if(dis.gt.0)then
stwb(stwbq:stwbq)=achar(aplus)
else if(dis.lt.0)then
stwb(stwbq:stwbq)=achar(aminus)
else
go to 80
end if
else if(igc.eq.62)then
if(dis.lt.0)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(aminus)
end if
else if(igc.eq.63)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(azero+int(qco(qcntr%e)))
else if(igc.eq.64)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(azero+int(qco(qcntr%t)))
else if(igc.eq.65)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(azero+int(qco(qcntr%p)))
else if(igc.eq.66)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(azero+int(qco(qcntr%c)))
else
go to 80
end if
else
jjj=0
if(igc.lt.72)then
if(igc.eq.67)then
jj=loopx(1)
else if(igc.eq.68)then
jj=loopx(2)
else if(igc.eq.69)then
jj=nloop
else if(igc.eq.70)then
jj=ndsym(symt%i)
jjj=1
if(jj.gt.1)then
stwbq=stwbq+2
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq-1:stwbq)=achar(azero+1)//achar(aslash)
end if
else if(igc.eq.71)then
jj=ndsym(symt%i)
jjj=1
end if
else if(igc.lt.77)then
if(igc.eq.72)then
jj=ndsym(symt%nl)
else if(igc.eq.73)then
jj=ndsym(symt%l)
else if(igc.eq.74)then
jj=nli-nleg
else if(igc.eq.76)then
jj=n-nleg
end if
else
if(igc.eq.77)then
jj=nleg
else if(igc.eq.78)then
jj=inco
else if(igc.eq.79)then
jj=outg
end if
end if
if(igc.eq.80)then
ip=stwbq+1
stwbq=stwbq+qcol(dcoty%off)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(qcop(dcoty%off)+1:qcop(dcoty%off)+qcol(dcoty%off))
else if(igc.eq.81)then
ip=stwbq+1
stwbq=stwbq+qcol(dcoty%nat)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(qcop(dcoty%nat)+1:qcop(dcoty%nat)+qcol(dcoty%nat))
else if(igc.eq.82)then
ip=stwbq+1
stwbq=stwbq+qcol(dcoty%offix)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(qcop(dcoty%offix)+1:qcop(dcoty%offix)+qcol(dcoty%offix))
else if(igc.eq.86)then
if(stib(momel(0)).gt.0)then
ip=stwbq+1
stwbq=stwbq+stib(momel(0))
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(stib(momep(0)):stib(momeq(0)))
end if
else if(igc.eq.87)then
if(stib(momzl(0)).gt.0)then
ip=stwbq+1
stwbq=stwbq+momzl(0)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(momzp(0):momzq(0))
end if
else
if(jjj.eq.0)then
call qdkar(jj,jk)
Q_ERRT
else
call qxdkar(jj,jk)
Q_ERRT
end if
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
end if
end if
else if(igk.eq.-4)then
if((lupt.eq.stylo%p).or.&
(luptt.eq.stylo%p))then
if(igc.lt.40)then
if(abs(igc-32).eq.1)then
i=lupi
j=pmap(ex(i),ey(i))
if(igc.eq.33)then
j=stib(link(0)+j)
end if
il=stib(namel(0)+j)
ip=stwbq+1
stwbq=stwbq+il
if(stwbq.gt.stwbu)then
go to 85
end if
ia=stib(namep(0)+j)
stwb(ip:stwbq)=stcb(ia:ia-1+il)
else if((abs(igc-37).eq.1).or.&
(abs(igc-36).eq.1))then
if(lupk.gt.0)then
if(igc.eq.36)then
ikm=-1
else
ikm=1
end if
else
if(igc.eq.35)then
ikm=-1
else
ikm=1
end if
kf=0
end if
j1=nleg+lupi
do i1=nleg+max(lupk,1),nleg+rhop2
if(i1.gt.rhop2)then
i2=i1-rhop2
ij=oflow(j1,i2)
else
i2=i1
ij=flow(j1,i2)
end if
if(ij.eq.0)then
if(lupk.gt.0)then
lupk=lupk+1
end if
else
ij=ikm*ij
j3=ex(lupi)
j4=ey(lupi)
j2=vmap(j3,j4)
if(j2.lt.j3)then
ij=-ij
else if(j2.eq.j3)then
if(modulo(j4-rdeg(j3),2).ne.0)then
ij=-ij
end if
end if
if((kf.ne.0).or.&
(ij.lt.0))then
ip=stwbq+1
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
if(ij.lt.0)then
stwb(ip:stwbq)=achar(aminus)
else
stwb(ip:stwbq)=achar(aplus)
end if
end if
ip=stwbq+1
if(i2.gt.nleg)then
stwbq=stwbq+stib(momel(0))
else
stwbq=stwbq+stib(momel(0)+i2)
end if
if(stwbq.gt.stwbu)then
go to 85
end if
if(i2.gt.nleg)then
stwb(ip:stwbq)=stcb(stib(momep(0)):stib(momeq(0)))
call qdkar(i2-nleg,jk)
Q_ERRT
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
else
stwb(ip:stwbq)=stcb(stib(momep(0)+i2):stib(momeq(0)+i2))
end if
kf=1
if(lupk.gt.0)then
exit
end if
end if
end do
if(kf.eq.0)then
if(stib(momzl(0)).gt.0)then
ip=stwbq+1
stwbq=stwbq+momzl(0)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(momzp(0):momzq(0))
end if
end if
go to 70
else if(igc.eq.32)then
i=lupi
j=pmap(ex(i),ey(i))
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
if(stib(antiq(0)+j).eq.0)then
stwb(stwbq:stwbq)=achar(aplus)
else
stwb(stwbq:stwbq)=achar(aminus)
end if
else if(igc.eq.34)then
jj=3
j1=stib(xstypp(0)+jj)
j2=stib(xstypl(0)+jj)
ip=stwbq+1
stwbq=stwbq+j2
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(j1:j1+(j2-1))
else
go to 80
end if
else if(igc.lt.60)then
if(igc.lt.45)then
if(igc.eq.40)then
jj=3
else if(igc.eq.41)then
jj=lupi
else if(igc.eq.42)then
jj=2*lupi-1
else if(igc.eq.43)then
i=lupi
j=ey(i)
i=ex(i)
jj=iovm(i,j)
else if(igc.eq.44)then
i=lupi
jj=ex(i)-nleg
else
go to 80
end if
else if(igc.lt.50)then
if(igc.eq.45)then
jj=2*lupi
else if(igc.eq.46)then
i=lupi
j=lmap(ex(i),ey(i))
i=vmap(ex(i),ey(i))
jj=iovm(i,j)
else if(igc.eq.47)then
i=lupi
jj=vmap(ex(i),ey(i))-nleg
else if(igc.eq.48)then
i=lupi
jj=vdeg(ex(i))
else if(igc.eq.49)then
i=lupi
jj=vdeg(vmap(ex(i),ey(i)))
else
go to 80
end if
else
if(igc.eq.55)then
jj=2*lupi-1+deltasub
else if(igc.eq.57)then
jj=2*lupi+deltasub
else
go to 80
end if
end if
call qdkar(jj,jk)
Q_ERRT
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
else
go to 80
end if
else if((lupt.eq.stylo%i).or.&
(lupt.eq.stylo%o))then
if(igc.lt.40)then
if(abs(igc-32).eq.1)then
i=lupi
j=stib(leg(0)+i)
if(igc.eq.31)then
j=stib(link(0)+j)
end if
if(lupi.gt.inco)then
j=stib(link(0)+j)
end if
il=stib(namel(0)+j)
ip=stwbq+1
stwbq=stwbq+il
if(stwbq.gt.stwbu)then
go to 85
end if
ia=stib(namep(0)+j)
stwb(ip:stwbq)=stcb(ia:ia-1+il)
else if(abs(igc-36).eq.1)then
i=lupi
if(igc.eq.37)then
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(stwbq:stwbq)=achar(aminus)
end if
ip=stwbq+1
stwbq=stwbq+stib(momel(0)+i)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(stib(momep(0)+i):stib(momeq(0)+i))
else if(igc.eq.32)then
i=lupi
j=stib(leg(0)+i)
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
if(stib(antiq(0)+j).eq.0)then
stwb(stwbq:stwbq)=achar(aplus)
else
stwb(stwbq:stwbq)=achar(aminus)
end if
else if(igc.eq.34)then
i=lupi
if(i.gt.inco)then
jj=2
else
jj=1
end if
j1=stib(xstypp(0)+jj)
j2=stib(xstypl(0)+jj)
ip=stwbq+1
stwbq=stwbq+j2
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(j1:j1+(j2-1))
else
go to 80
end if
else if(igc.lt.50)then
if(igc.eq.40)then
i=lupi
if(i.gt.inco)then
jj=2
else
jj=1
end if
else if(igc.eq.42)then
i=lupi
if(i.gt.inco)then
jj=2*(inco-i)
else
jj=1-2*i
end if
else if(igc.eq.43)then
i=lupi
j=lmap(invps1(i),1)
i=vmap(invps1(i),1)
jj=iovm(i,j)
else if(igc.eq.44)then
i=lupi
jj=vmap(invps1(i),1)-nleg
else if(igc.eq.48)then
i=lupi
j=lmap(invps1(i),1)
jj=vdeg(vmap(invps1(i),1))
else
go to 80
end if
call qdkar(jj,jk)
Q_ERRT
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
else if(igc.lt.60)then
if(igc.eq.52)then
i=lupi
else if(igc.eq.53)then
i=lupi-inco
else if(igc.eq.54)then
i=lupi
else if(igc.eq.55)then
if(lupi.gt.inco)then
i=2*(lupi-inco)
else
i=2*lupi-1
end if
else
go to 80
end if
call qdkar(i,jk)
Q_ERRT
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
else
go to 80
end if
else if((lupt.eq.stylo%v).or.&
(lupt.eq.stylo%r).or.&
(luptt.eq.stylo%r))then
if(igc.lt.40)then
if(abs(igc-32).eq.1)then
i=nleg+lupi
j=lupj
j=pmap(i,ovm(i,j))
if(igc.eq.33)then
j=stib(link(0)+j)
end if
il=stib(namel(0)+j)
ip=stwbq+1
stwbq=stwbq+il
if(stwbq.gt.stwbu)then
go to 85
end if
ia=stib(namep(0)+j)
stwb(ip:stwbq)=stcb(ia:ia-1+il)
else if((abs(igc-37).eq.1).or.&
(abs(igc-36).eq.1))then
if(lupk.eq.0)then
kf=0
end if
if(kf.eq.0)then
j1=nleg+lupi
j2=ovm(j1,lupj)
jj=amap(j1,j2)
kk=vmap(j1,j2)
if(igc.lt.37)then
ikm=-1
else
ikm=1
end if
if(kk.lt.j1)then
if(kk.gt.nleg)then
ikm=-ikm
else if(ps1(kk).le.inco)then
ikm=-ikm
end if
else if(kk.eq.j1)then
if(lmap(j1,j2).gt.j2)then
ikm=-ikm
end if
end if
end if
do i1=nleg+max(lupk,1),nleg+rhop2
if(i1.gt.rhop2)then
i2=i1-rhop2
ij=oflow(jj,i2)
else
i2=i1
ij=flow(jj,i2)
end if
if(ij.eq.0)then
if(lupk.gt.0)then
lupk=lupk+1
end if
else
ij=ikm*ij
if((kf.ne.0).or.&
(ij.lt.0))then
ip=stwbq+1
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
if(ij.lt.0)then
stwb(ip:stwbq)=achar(aminus)
else
stwb(ip:stwbq)=achar(aplus)
end if
end if
ip=stwbq+1
if(i2.gt.nleg)then
stwbq=stwbq+stib(momel(0))
else
stwbq=stwbq+stib(momel(0)+i2)
end if
if(stwbq.gt.stwbu)then
go to 85
end if
if(i2.gt.nleg)then
stwb(ip:stwbq)=stcb(stib(momep(0)):stib(momeq(0)))
call qdkar(i2-nleg,jk)
Q_ERRT
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
else
stwb(ip:stwbq)=stcb(stib(momep(0)+i2):stib(momeq(0)+i2))
end if
kf=1
if(lupk.gt.0)then
exit
end if
end if
end do
if(kf.eq.0)then
if(stib(momzl(0)).gt.0)then
ip=stwbq+1
stwbq=stwbq+momzl(0)
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(momzp(0):momzq(0))
end if
end if
go to 70
else if(igc.eq.32)then
i=nleg+lupi
j=lupj
j=pmap(i,ovm(i,j))
stwbq=stwbq+1
if(stwbq.gt.stwbu)then
go to 85
end if
if(stib(antiq(0)+j).eq.0)then
stwb(stwbq:stwbq)=achar(aplus)
else
stwb(stwbq:stwbq)=achar(aminus)
end if
else if(igc.eq.34)then
i=nleg+lupi
j=lupj
j=ovm(i,j)
ij=vmap(i,j)
if(ij.gt.nleg)then
jj=3
else
if(ps1(ij).gt.inco)then
jj=2
else
jj=1
end if
end if
j1=stib(xstypp(0)+jj)
j2=stib(xstypl(0)+jj)
ip=stwbq+1
stwbq=stwbq+j2
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(j1:j1+(j2-1))
else
go to 80
end if
else if(igc.lt.60)then
if(igc.eq.41)then
i=nleg+lupi
j=lupj
j=ovm(i,j)
ij=vmap(i,j)
if(ij.gt.nleg)then
jj=amap(i,j)-nleg
else
ij=ps1(ij)
if(ij.gt.inco)then
jj=2*(inco-ij)
else
jj=1-2*ij
end if
end if
else if(igc.lt.46)then
if(igc.eq.40)then
i=nleg+lupi
j=lupj
j=ovm(i,j)
ij=vmap(i,j)
if(ij.gt.nleg)then
jj=3
else
if(ps1(ij).gt.inco)then
jj=2
else
jj=1
end if
end if
else if((igc.eq.42).or.&
(igc.eq.45))then
i=nleg+lupi
j=lupj
j=ovm(i,j)
ij=vmap(i,j)
if(ij.gt.nleg)then
kk=amap(i,j)-nleg
if((ex(kk).eq.i).and.&
(ey(kk).eq.j))then
jj=2*kk-1
else
jj=2*kk
end if
else
ij=ps1(ij)
if(ij.gt.inco)then
jj=2*(inco-ij)
else
jj=1-2*ij
end if
end if
if(igc.eq.45)then
if(jj.gt.0)then
jj=jj-1+2*modulo(jj,2)
else
jj=0
end if
end if
else if(igc.eq.43)then
jj=lupj
else if(igc.eq.44)then
jj=lupi
else
go to 80
end if
else
if(igc.eq.46)then
i=nleg+lupi
j=lupj
ij=ovm(i,j)
ii=vmap(i,ij)
if(ii.gt.nleg)then
jj=iovm(ii,lmap(i,ij))
else
jj=0
end if
else if(igc.eq.47)then
i=nleg+lupi
j=lupj
jj=vmap(i,ovm(i,j))-nleg
if(jj.lt.0)then
jj=0
end if
else if(igc.eq.48)then
jj=vdeg(nleg+lupi)
else if(igc.eq.49)then
i=nleg+lupi
j=lupj
jj=vmap(i,ovm(i,j))
if(jj.gt.nleg)then
jj=vdeg(jj)
else
jj=0
end if
else if(abs(igc-56).eq.1)then
i=nleg+lupi
j=lupj
j=ovm(i,j)
ij=vmap(i,j)
if(ij.gt.nleg)then
kk=amap(i,j)-nleg
if((ex(kk).eq.i).and.&
(ey(kk).eq.j))then
jj=2*kk-1
else
jj=2*kk
end if
else
ij=ps1(ij)
if(ij.gt.inco)then
jj=2*(inco-ij)
else
jj=1-2*ij
end if
end if
if(igc.eq.57)then
if(jj.gt.0)then
jj=jj-1+2*modulo(jj,2)
else
jj=0
end if
end if
if(jj.gt.0)then
jj=deltasub+jj
else
jj=-jj
end if
else
go to 80
end if
end if
call qdkar(jj,jk)
Q_ERRT
ip=stwbq+1
stwbq=stwbq+jk
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=zstr(1:jk)
else
go to 80
end if
else
go to 80
end if
else
go to 80
end if
else if(igk.eq.-6)then
igc=stib(ig+1)
if((igc.le.0).or.&
(igc.gt.nudk))then
go to 80
end if
igut=stib(udkt(0)+igc)
if(lupt.eq.stylo%m)then
if(lupti(0).gt.1)then
elupt=luptt
else
go to 80
end if
else
elupt=lupt
end if
if(igut.eq.1)then
ij=stib(udki(0)+igc)
if((ij.le.0).or.&
(ij.gt.ngmk))then
go to 80
end if
j1=stib(gmkvp(0)+ij)
j2=stib(gmkvl(0)+ij)
if(j2.gt.0)then
ip=stwbq+1
stwbq=stwbq+j2
if(stwbq.gt.stwbu)then
go to 85
end if
stwb(ip:stwbq)=stcb(j1:j1-1+j2)
else if((j2.lt.0).or.&
(stib(ig+3).ne.0))then
go to 80
end if
else if(igut.eq.2)then
if(elupt.eq.stylo%i)then
i=lupi
j=stib(link(0)+stib(leg(0)+i))
else if(elupt.eq.stylo%o)then
i=lupi
j=stib(leg(0)+i)
else if(elupt.eq.stylo%p)then
i=lupi
j=pmap(ex(i),ey(i))
else if(elupt.eq.stylo%v)then
go to 80
else if(elupt.eq.stylo%r)then
i=nleg+lupi
j=lupj
j=pmap(i,ovm(i,j))
else
go to 80
end if
if(stib(ig+3).ne.0)then
j=stib(link(0)+j)
end if
if((j.le.0).or.&
(j.gt.nphi))then
go to 80
end if
ij=stib(udki(0)+igc)
if((ij.le.0).or.&
(ij.gt.npmk))then
go to 80
end if
il=stib(stib(pmkvflp(0)+j)+ij)
if(il.gt.0)then
ip=stwbq+1
stwbq=stwbq+il
if(stwbq.gt.stwbu)then
go to 85
end if
ia=stib(stib(pmkvfpp(0)+j)+ij)
stwb(ip:stwbq)=stcb(ia:ia-1+il)
else if(il.lt.0)then
go to 80
end if
else if(igut.eq.3)then
if((elupt.eq.stylo%i).or.&
(elupt.eq.stylo%o))then
i=lupi
jj=vmap(invps1(i),1)
else if(elupt.eq.stylo%p)then
i=lupi
if(stib(ig+3).eq.0)then
jj=ex(i)
else
jj=vmap(ex(i),ey(i))
end if
else if(elupt.eq.stylo%v)then
jj=nleg+lupi
else if(elupt.eq.stylo%r)then
jj=nleg+lupi
else
go to 80
end if
j=stib(vfo(jj))
ij=stib(udki(0)+igc)
if((ij.le.0).or.&
(ij.gt.nvmk))then
go to 80
else if((j.le.0).or.&
(j.gt.nvert))then
go to 80
end if
il=stib(stib(vmkvlp(0)+ij)+j)
if(il.gt.0)then
ip=stwbq+1
stwbq=stwbq+il
if(stwbq.gt.stwbu)then
go to 85
end if
ia=stib(stib(vmkvpp(0)+ij)+j)
stwb(ip:stwbq)=stcb(ia:ia-1+il)
else if(il.lt.0)then
go to 80
end if
else
go to 80
end if
else if(igk.eq.eosf)then
if(lupt.ne.0)then
go to 80
end if
if(filt(f0).eq.qfty%ptyp)then
#ifdef Q_API
stwbqf(f1)=stwbq
call qpout(f0)
Q_ERRT
#endif
else if(cflag(confi%nontlf).ne.0)then
stwbqf(f1)=stwbq
call qout(f0)
Q_ERRT
stwbqf(f1)=stwbpf(f1)
else if(stwbq.gt.stwbp)then
if(stwbq.lt.stwbt)then
stwbqf(f1)=stwbq
else if(stwbq.lt.stwbu)then
stwbqf(f1)=stwbq
call qout(f0)
Q_ERRT
stwbqf(f1)=stwbpf(f1)
else
go to 80
end if
end if
go to 01
else
go to 80
end if
70 continue
ig=ig+stib(ig+2)
go to 10
80 continue
qerrt(0)=qerrty%q
call qstymsg(11,0,0,0,0,0)
Q_ERRT
85 continue
qerrt(0)=qerrty%q
#ifdef Q_API
f1x=f1
call qpomsg(3)
Q_ERRT
#else
call quput(7)
Q_ERRT
#endif
99 continue
return
end subroutine qompac
subroutine qflow
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qsty
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::i1,i2,ij,j1,j2,j3,j4,j5
if(nleg.gt.0)then
do i1=1,nli
do i2=1,rho(-1)
oflow(i1,i2)=0
end do
end do
end if
do i1=1,nli
if(i1.gt.nleg)then
j1=ex0(i1-nleg)
j2=ey0(i1-nleg)
ij=vmap(j1,j2)
if(ij.ne.j1)then
do i2=1,nleg
j3=flow(i1,invps1(i2))
if(i2.gt.inco)then
oflow(i1,i2)=-j3
else
oflow(i1,i2)=j3
end if
end do
end if
else
ij=ps1(i1)
oflow(i1,ps1(i1))=1
end if
end do
if(cflag(confi%hidpq).ne.0)then
if(rho(-1).gt.0)then
j1=cflag(confi%hidpq)
if(j1.gt.inco)then
j2=-1
else
j2=1
end if
do i1=1,nli
j4=oflow(i1,j1)
if(j4.ne.0)then
do i2=1,rho(-1)
j3=ps1(i2)
if(j3.gt.inco)then
j5=-j2*j4
else
j5=j2*j4
end if
oflow(i1,j3)=oflow(i1,j3)-j5
end do
end if
end do
end if
end if
99 continue
return
end subroutine qflow
subroutine qifi
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::i1,i2,j1,j2
do i1=2,nfiles-1
if(filt(i1).eq.qfty%otyp)then
if(dso.ne.0)then
if(filt(i1+dso).ne.qfty%styp)then
qerrt(0)=qerrty%inp
call qcfmsg(8,0,0)
Q_ERRT
end if
end if
else if(filt(i1).eq.qfty%ptyp)then
if(qxmod.eq.qmod%api)then
if(filp(i1).eq.nap)then
filt(i1)=qfty%ptyp
fild(i1)=qfdty%dno
filp(i1)=0
filq(i1)=0
end if
end if
end if
end do
do i1=1,nfiles-1
if((filp(i1).ne.nap).and.&
(filp(i1).ne.0))then
j1=filq(i1)-filp(i1)
do i2=i1+1,nfiles
if(filt(i2).eq.filt(i1))then
if(filp(i2).ne.nap)then
if(j1.eq.filq(i2)-filp(i2))then
if(stcb(filp(i1):filq(i1)).eq.stcb(filp(i2):filq(i2)))then
qerrt(0)=qerrty%inp
call qcfmsg(11,0,0)
Q_ERRT
end if
end if
end if
end if
end do
end if
end do
film(:)=0
do i1=1,nfiles
if(film(i1).eq.0)then
j1=1
film(i1)=j1
j2=filt(i1)
do i2=i1+1,nfiles
if(filt(i2).eq.j2)then
j1=j1+1
film(i2)=j1
end if
end do
end if
end do
if(qxmod.eq.qmod%api)then
j1=0
do i1=1,nfiles
if((filt(i1).eq.qfty%otyp).or.&
(filt(i1).eq.qfty%ptyp))then
j1=j1+1
film(i1)=j1
end if
end do
end if
j1=0
do i1=1,nfiles
if(filt(i1).eq.qfty%ptyp)then
j1=j1+1
filo(i1)=j1
end if
end do
do i1=1,nfiles
if(filt(i1).eq.qfty%otyp)then
j1=j1+1
filo(i1)=j1
end if
end do
99 continue
return
end subroutine qifi
subroutine qstyle
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstyki,qudstyk
character(kind=asciik,len=srec)::styb
integer(kind=c_int_least32_t)::f0,f1,ieosf,isec,lgm,slin
integer(kind=c_int_least32_t)::ii,ij,i1,jj,j1,j2,kp1,kp2,k1,k2
integer(kind=c_int_least32_t)::clin(1:sfiles0),nlin(1:sfiles0),cccf(1:sfiles0)
integer(kind=c_int_least32_t)::dlin(1:sfiles0),ddlin(1:sfiles0)
j1=0
do i1=1,nfiles
if(filt(i1).eq.qfty%styp)then
if(filp(i1).ne.nap)then
call qopen(i1)
Q_ERRT
end if
j1=j1+1
nlin(j1)=0
dlin(j1)=0
ddlin(j1)=0
end if
end do
ks=0
call qaoib(2)
Q_ERRT
udkp(1)=stibs(1)-1
stib(udkp(1))=eoa
stib(stibs(1))=eoa
isec=-1
cccf(:)=-1
04 continue
if(isec.gt.0)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=eosf
end if
isec=isec+1
if(isec.gt.4)then
call qrsfki
Q_ERRT
go to 99
end if
if(isec.gt.0)then
iogp(isec)=stibs(1)+1
end if
ieosf=0
f0=0
10 continue
f0=f0+1
if(f0.gt.nfiles)then
go to 04
else if(filp(f0).eq.nap)then
go to 10
else if(filt(f0).ne.qfty%styp)then
go to 10
end if
f1=film(f0)
if(abs(isec-2).lt.2)then
call qaoib(2)
Q_ERRT
if(f1.gt.1)then
stib(ieosf)=stibs(1)-ieosf
end if
ieosf=stibs(1)
stib(ieosf-1)=eosf
end if
clin(f1)=0
jflag(jflaty%backmod)=1
20 continue
call qrr(f0,nlin(f1))
Q_ERRT
recdty(recty%annot)=0
slin=recdty(recty%len)
if(slin.lt.0)then
if(isec.lt.4)then
call qstymsg(1,0,0,f0,0,0)
Q_ERRT
end if
go to 10
else if(slin.eq.0)then
if(abs(isec-2).lt.2)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=alf
end if
go to 20
end if
styb(1:slin+1)=stcb(stcbs(1)+1:stcbs(1)+slin)//achar(alf)
ij=0
if(clin(f1).eq.0)then
j1=iachar(styb(1:1))
j2=iachar(styb(slin:slin))
if((j1.eq.alt).and.&
(j2.eq.agt))then
ij=qstyki(styb,2,slin-1,isec)
Q_ERRT
if((ij.gt.0).and.&
(ij.ne.24).and.&
(ij.ne.25))then
if(stib(kla(0)+ij).eq.0)then
if(ij-1.ne.isec)then
go to 80
else if(ks.ne.0)then
go to 80
end if
if(ij.eq.1)then
dlin(f1)=nlin(f1)+1
end if
if(recdty(recty%xchar).ne.0)then
go to 80
end if
go to 10
end if
end if
end if
end if
if(recdty(recty%xchar).ne.0)then
if((cflag(confi%xchar).lt.0).or.&
(abs(isec-2).lt.2))then
qerrt(0)=qerrty%inp
call qiomsg(17,nlin(f1),nlin(f1),f0)
Q_ERRT
end if
end if
if(abs(isec-2).eq.2)then
j1=iachar(styb(1:1))
if(acf(j1).eq.chty%annot)then
recdty(recty%annot)=1
if(j1.eq.aast)then
qerrt(0)=qerrty%inp
call qiomsg(14,nlin(f1),nlin(f1),f0)
Q_ERRT
else if(fila(f0).eq.0)then
fila(f0)=j1
else if(fila(f0).ne.j1)then
qerrt(0)=qerrty%inp
call qiomsg(16,nlin(f1),nlin(f1),f0)
Q_ERRT
end if
end if
ii=1
if(cccf(f1).gt.0)then
if(recdty(recty%annot).ne.0)then
ii=0
else
go to 80
end if
else if(cccf(f1).lt.0)then
if(recdty(recty%annot).ne.0)then
cccf(f1)=1
ii=0
end if
end if
if(ii.eq.0)then
go to 20
end if
j1=iachar(styb(1:1))
j2=iachar(styb(slin:slin))
if((j1.eq.alt).and.&
(j2.eq.agt))then
ii=qstyki(styb,2,slin-1,isec)
Q_ERRT
if(ii.eq.24)then
if(cccf(f1).lt.0)then
cccf(f1)=0
end if
if(clin(f1).ne.0)then
go to 80
else
clin(f1)=nlin(f1)
go to 20
end if
else if(ii.eq.25)then
if(cccf(f1).ne.0)then
go to 80
else if(clin(f1).eq.0)then
go to 80
else
clin(f1)=0
go to 20
end if
else if((isec.eq.0).and.&
(clin(f1).eq.0).and.&
(ii.eq.1))then
go to 10
else if(cccf(f1).ne.0)then
go to 80
else
go to 20
end if
end if
else if(clin(f1).ne.0)then
go to 80
end if
j1=0
j2=0
k1=0
k2=0
kp1=0
kp2=0
lgm=0
do i1=1,slin
jj=iachar(styb(i1:i1))
if((j2.eq.0).and.&
(jj.eq.alt))then
j1=j1+1
if(j1.eq.2)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=jj
j1=0
else if(iachar(styb(i1+1:i1+1)).ne.alt)then
if(lgm.ne.0)then
go to 80
end if
lgm=1-lgm
kp1=i1+1
end if
else if((j1.eq.0).and.&
(jj.eq.alsbr))then
j2=j2+1
if(j2.eq.2)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=jj
j2=0
else if(iachar(styb(i1+1:i1+1)).ne.alsbr)then
if(j1.ne.0)then
go to 80
else if(lgm.ne.0)then
go to 80
end if
lgm=1-lgm
kp1=i1+1
end if
else if((j2.eq.0).and.&
(jj.eq.agt))then
if(j1.eq.0)then
k1=k1+1
if(k1.eq.2)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=jj
k1=0
else if(iachar(styb(i1+1:i1+1)).ne.agt)then
go to 80
end if
else
if(lgm.eq.0)then
go to 80
end if
lgm=1-lgm
j1=0
kp2=i1-1
if(kp2-kp1.lt.0)then
go to 80
end if
ii=qstyki(styb,kp1,kp2,isec)
Q_ERRT
if(ii.gt.99)then
ii=0
end if
if(ii.eq.91)then
go to 80
else if(nlin(f1).eq.dlin(f1))then
if(ddlin(f1).lt.2)then
ddlin(f1)=ddlin(f1)+2
end if
end if
if(ii.le.0)then
go to 80
else if(ii.lt.5)then
if((kp1.ne.2).or.&
(kp2+1.ne.slin))then
go to 80
else if((ks.ne.0).or.&
(clin(f1).ne.0))then
go to 80
end if
else if(ii.eq.24)then
if(clin(f1).ne.0)then
go to 80
end if
if(abs(isec-2).eq.2)then
if((kp1.ne.2).or.&
(kp2+1.ne.slin))then
go to 80
end if
end if
clin(f1)=nlin(f1)
else if(ii.eq.25)then
if(clin(f1).eq.0)then
go to 80
end if
if(abs(isec-2).eq.2)then
if((kp1.ne.2).or.&
(kp2+1.ne.slin))then
go to 80
end if
end if
clin(f1)=0
else if(clin(f1).eq.0)then
call qktoc(isec,ii,nlin(f1),f0)
Q_ERRT
else
qerrmsg(1:srec)='qstyle_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
else if((j1.eq.0).and.&
(jj.eq.arsbr))then
if(j2.eq.0)then
k2=k2+1
if(k2.eq.2)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=jj
k2=0
else if(iachar(styb(i1+1:i1+1)).ne.arsbr)then
go to 80
end if
else
j2=0
if(j1.ne.0)then
go to 80
else if(lgm.eq.0)then
go to 80
end if
lgm=1-lgm
kp2=i1-1
if(kp2-kp1.lt.0)then
go to 80
end if
if(clin(f1).ne.0)then
qerrmsg(1:srec)='qstyle_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=qudstyk(styb,kp1,kp2)
Q_ERRT
if(ii.eq.0)then
go to 80
end if
end if
else if((j1.eq.0).and.&
(j2.eq.0))then
if(clin(f1).eq.0)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=jj
else if(jj.ne.aspc)then
if(abs(isec-2).lt.2)then
go to 80
end if
end if
end if
end do
if(lgm.ne.0)then
go to 80
end if
if(clin(f1).ne.0)then
go to 20
end if
call qaoib(1)
Q_ERRT
stib(stibs(1))=alf
go to 20
80 continue
if(clin(f1).eq.0)then
ii=nlin(f1)
else
ii=clin(f1)
end if
qerrmsg(1:srec)="wrong syntax,"//achar(anull)
qerrt(0)=qerrty%inp
call qmput(ii,nlin(f1),f0)
Q_ERRT
99 continue
return
end subroutine qstyle
subroutine qktoc(isec,kco,nlin,ifile)
use,non_intrinsic::qfcon
use,non_intrinsic::qintr
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::isec,kco,nlin,ifile
integer(kind=c_int_least32_t), external::qlupty,qluptyfc
integer(kind=c_int_least32_t)::astak(1:maxtak)
integer(kind=c_int_least32_t)::i1,ii,ik,j1,j2,ka,kk,kt,lupt
ka=-1
do i1=1,nske
if(stib(kc(0)+i1).eq.kco)then
ik=i1
ka=stib(kla(0)+i1)
j1=stib(pske(0)+i1)-1
j2=stib(wske(0)+i1)
exit
end if
end do
serrt=qerrty%ok
if(max(3,5,3,6).gt.maxpot)then
serrt=qerrty%q
else if(abs(isec-2).gt.1)then
serrt=qerrty%q
else if(abs(ka-3).gt.2)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qktoc_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
kk=stib(klo(0)+ik)
if(ks.eq.0)then
if(kk.ne.0)then
go to 80
end if
else if(kk.ne.0)then
if(tak(ks).gt.0)then
ii=tak(ks)
else
ii=tak(ks)+3
end if
if(modulo(kk,pot(ii)).lt.pot(ii-1))then
go to 80
end if
else if(ka.eq.1)then
go to 80
end if
if(ka.eq.1)then
if(tofc.eq.0)then
lupt=qlupty(kco)
Q_ERRT
else
lupt=qluptyfc(kco)
end if
if(lupt.eq.stylo%m)then
kt=0
end if
if(lupt.ne.stylo%end)then
if(ks.ge.maxtak)then
call qstymsg(9,nlin,nlin,0,0,0)
Q_ERRT
end if
if((lupt.eq.stylo%sti).and.&
(abs(isec-2).eq.1))then
if(tak(1).ne.stylo%sto)then
go to 80
end if
else if(lupt.eq.stylo%r)then
if(tak(1).ne.stylo%v)then
go to 80
end if
else if(lupt.ne.stylo%m)then
if(ks.ne.0)then
go to 80
end if
end if
ii=stibs(1)+1
call qaoib(6)
Q_ERRT
stib(ii)=-ka
stib(ii+1)=lupt
stib(ii+2)=6
stib(ii+3)=0
stib(ii+4)=0
stib(stibs(1))=0
ks=ks+1
astak(ks)=ii
tak(ks)=lupt
else
if(ks.le.0)then
go to 80
else if(kt.gt.1)then
go to 80
end if
call qaoib(3)
Q_ERRT
ii=stibs(1)-astak(ks)
stib(stibs(1)-2)=-ka
stib(stibs(1)-1)=stylo%end
stib(stibs(1))=2-ii
stib(astak(ks)+3)=ii
ks=ks-1
end if
else if(ka.eq.5)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=alf
else
call qaoib(3)
Q_ERRT
stib(stibs(1)-2)=-ka
stib(stibs(1)-1)=kco
stib(stibs(1))=3
end if
if(kco.eq.41)then
if(ks.gt.1)then
if(tak(ks).eq.stylo%m)then
if(tak(ks-1).eq.stylo%r)then
go to 80
end if
end if
end if
end if
if(abs(kco-37).eq.1)then
kt=kt+1
end if
go to 99
80 continue
qerrmsg(1:srec)="wrong syntax,"//achar(anull)
qerrt(0)=qerrty%inp
call qmput(nlin,nlin,ifile)
Q_ERRT
99 continue
return
end subroutine qktoc
integer(kind=c_int_least32_t) function qstykifc(s,s1,s2,jsec)
use,non_intrinsic::qfcon
use,non_intrinsic::qintr
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::s1,s2,jsec
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::ij
qstykifc=0
if(s1.gt.s2)then
qerrmsg(1:srec)='qstykifc_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ij=0
call qmstr0(s,s1,s2,pske(0),wske(0),aske(0),ij)
Q_ERRT
if(ij.le.0)then
go to 99
else
qstykifc=stib(kc(0)+ij)
end if
if(qstykifc.le.4)then
if(qstykifc.ne.jsec+1)then
qstykifc=0
end if
else if(abs(jsec-2)-1.le.0)then
if(modulo(stib(kse(0)+ij),pot(jsec)).lt.pot(jsec-1))then
qstykifc=0
end if
end if
if(qstykifc.gt.0)then
skep(qstykifc)=1
end if
99 continue
return
end function qstykifc
integer(kind=c_int_least32_t) function qstyki(s,s1,s2,jsec)
use,non_intrinsic::qfcon
use,non_intrinsic::qintr
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::s1,s2,jsec
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t)::ij
qstyki=0
if(s1.gt.s2)then
qerrmsg(1:srec)='qstyki_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ij=0
call qmstr0(s,s1,s2,pske(0),wske(0),aske(0),ij)
Q_ERRT
if(ij.le.0)then
go to 99
end if
qstyki=stib(kc(0)+ij)
if(qstyki.le.4)then
if(qstyki.ne.jsec+1)then
qstyki=0
end if
else if(abs(jsec-2)-1.le.0)then
if(modulo(stib(kse(0)+ij),pot(jsec)).lt.pot(jsec-1))then
qstyki=0
end if
end if
if(qstyki.gt.0)then
skep(qstyki)=1
end if
if((cflag(confi%qlist).gt.0).or.&
(qxmod.eq.qmod%api))then
if(ks.gt.0)then
if((tak(ks).eq.stylo%p).or.&
(tak(ks).eq.stylo%r))then
ij=skep(35)+skep(36)+skep(37)+skep(38)
if(ij.gt.0)then
jflag(jflaty%intlp)=1
jflag(jflaty%smom)=1
end if
end if
end if
end if
99 continue
return
end function qstyki
integer(kind=c_int_least32_t) function qudstyk(s,s1,s2)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::s1,s2
character(kind=asciik,len=*),intent(in)::s
integer(kind=c_int_least32_t), external::qstdw
integer(kind=c_int_least32_t)::i1,ii,j1,j2,j3,jj,kd,kt,kstep
qudstyk=0
if(ks.eq.0)then
kt=4
else
jj=ks
if(tak(jj).eq.6)then
jj=jj-1
end if
kt=max(tak(jj)+3,5)
if(kt.gt.8)then
go to 99
end if
end if
kd=0
j1=s1-1+dprefl
if(s2.ge.j1)then
if(s(s1:j1).eq.stcb(dprefp:dprefp-1+dprefl))then
if(s2.gt.j1)then
kd=1
else
go to 99
end if
end if
end if
j1=s1+kd*dprefl
jj=qstdw(s,j1,s2)
Q_ERRT
if(jj.eq.0)then
go to 99
end if
jj=s2-j1+1
if(nudk.gt.0)then
call qmstr1(s,j1,s2,udkp(1),1,2,qudstyk,ii)
Q_ERRT
end if
j2=stibs(1)
kstep=4
call qaoib(kstep)
Q_ERRT
stib(j2+1)=-6
if(qudstyk.eq.0)then
nudk=nudk+1
stib(j2+2)=nudk
else
stib(j2+2)=qudstyk
end if
stib(j2+3)=kstep
stib(j2+4)=kd
ii=udkp(1)
if(qudstyk.ne.0)then
do i1=1,qudstyk
ii=stib(ii)
end do
j2=ii-1+kt
if(stib(j2).eq.0)then
stib(j2)=1+kd
else if(stib(j2).eq.2-kd)then
stib(j2)=3
end if
go to 99
end if
qudstyk=stib(j2+2)
do i1=2,nudk
ii=stib(ii)
end do
j3=stcbs(1)+1
call qaocb(jj+1)
Q_ERRT
stcb(j3:stcbs(1))=s(j1:s2)//achar(anull)
j2=stibs(1)
kstep=8
call qaoib(kstep)
Q_ERRT
stib(j2-1)=stib(j2-1)+kstep
stib(ii)=j2+1
stib(j2+1)=eoa
stib(j2+2)=j3
stib(j2+3)=jj
stib(j2+4:j2+8)=0
stib(j2+kt)=kd+1
99 continue
return
end function qudstyk
integer(kind=c_int_least32_t) function qlupty(ll)
use,non_intrinsic::qsty
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ll
integer(kind=c_int_least32_t),parameter::lup1=11,lup2=19
qlupty=0
if((ll.lt.lup1).or.&
(ll.gt.lup2))then
qerrmsg(1:srec)='qlupty_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(ll.lt.13)then
qlupty=ll-13
else if(ll.lt.lup2)then
qlupty=ll-12
else
qlupty=stylo%end
end if
99 continue
return
end function qlupty
integer(kind=c_int_least32_t) function qluptyfc(ll)
use,non_intrinsic::qsty
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ll
integer(kind=c_int_least32_t),parameter::lup1=11,lup2=19,lup3=101,lup4=102
qluptyfc=0
if((ll.lt.lup1).or.&
(ll.gt.lup2))then
if((ll.lt.lup3).or.&
(ll.gt.lup4))then
qerrmsg(1:srec)='qluptyfc_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
if(ll.lt.13)then
qluptyfc=ll-13
else if(ll.lt.lup2)then
qluptyfc=ll-12
else if(ll.ge.lup3)then
qluptyfc=ll-103
else
qluptyfc=stylo%end
end if
99 continue
return
end function qluptyfc
subroutine qnapa(s,ia,ib,jf)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qzbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,jf
integer(kind=c_int_least32_t),intent(inout)::ib
character(kind=asciik,len=*),intent(inout)::s
integer(kind=c_int_least32_t), external::qstdw,qstdz,qstdq
integer(kind=c_int_least32_t)::i1,i2,ic,icc,ier,it,itt,j1,j2,j3,lch
integer(kind=c_int_least32_t)::strs,st0,s0,splic,dplic,bplic
serrt=qerrty%ok
if(ia.le.0)then
serrt=qerrty%q
else if(ib.lt.ia)then
serrt=qerrty%q
else if(iachar(s(ib:ib)).ne.alf)then
serrt=qerrty%q
else if((jf.ne.qfty%ctyp).and.&
(jf.ne.qfty%mtyp))then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qnapa_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
strs=1
call qvaojb(strs)
Q_ERRT
s0=stjbs+strs
stjb(s0)=0
st0=s0
j1=0
j2=0
splic=0
dplic=0
bplic=0
i1=ia-1
ic=0
lch=1
ier=0
do while(i1.lt.ib)
i1=i1+lch
lch=1
if(i1.le.ib)then
ic=iachar(s(i1:i1))
if(ic.eq.alf)then
if(bplic.ne.0)then
ier=1
exit
end if
else if(ic.eq.atab)then
ic=aspc
s(i1:i1)=achar(aspc)
end if
end if
icc=0
itt=0
if(i1.lt.ib)then
do i2=1,ncrs0
if(crs(i2,csyfty(jf)).ne.0)then
if(ic.eq.crs(i2,1))then
if(iachar(s(i1+1:i1+1)).eq.crs(i2,2))then
icc=crs(i2,3)
itt=crs(i2,4)
end if
exit
end if
end if
end do
end if
if(bplic.eq.0)then
if(icc.eq.dsq)then
icc=0
itt=0
else if(icc.ne.0)then
lch=lch+1
end if
else if(splic.ne.0)then
if(icc.eq.dsq)then
lch=lch+1
j2=j2+1
cycle
end if
end if
if(bplic.eq.0)then
if(itt.eq.0)then
itt=stib(punct1(0)+ic)
icc=ic
end if
if(itt.le.0)then
if(j1.eq.0)then
j1=i1
if(ic.eq.asq)then
splic=1
bplic=1
else if(ic.eq.adq)then
dplic=1
bplic=1
end if
else
j3=0
if(ic.eq.asq)then
j3=1
else if(ic.eq.adq)then
j3=1
end if
if(j3.ne.0)then
if(i1.gt.ia)then
if(ic.eq.iachar(s(i1-1:i1-1)))then
j3=0
end if
end if
end if
if(j3.ne.0)then
ier=1
exit
end if
end if
j2=i1
else
if(j2.ne.0)then
it=0
if(splic.ne.0)then
it=strty%sqs
splic=0
else if(dplic.ne.0)then
it=strty%dqs
dplic=0
else if(j1.eq.j2)then
it=abs(stib(punct1(0)+iachar(s(j1:j1))))
end if
if(it.eq.0)then
j3=qstdw(s,j1,j2)
Q_ERRT
if(j3.ne.0)then
it=strty%id
else
j3=qstdz(s,j1,j2,inty%h)
Q_ERRT
if(j3.ne.0)then
it=strty%z
if(qxmod.eq.qmod%fcon)then
if(stofc.gt.0)then
j3=qstdz(s,j1,j2,inty%s)
Q_ERRT
if(j3.eq.0)then
it=strty%sqs
if(ib.gt.stcbs(1))then
call qvaocb(2)
Q_ERRT
ib=ib+2
do i2=ib,j2+3,-1
stcb(i2:i2)=stcb(i2-2:i2-2)
end do
stcb(j2+2:j2+2)=achar(asq)
do i2=j2+1,j1+1,-1
stcb(i2:i2)=stcb(i2-1:i2-1)
end do
stcb(j1:j1)=achar(asq)
j2=j2+2
i1=i1+2
end if
end if
end if
end if
else
j3=qstdq(s,j1,j2,inty%h)
Q_ERRT
if(j3.ne.0)then
it=strty%q
if(qxmod.eq.qmod%fcon)then
if(stofc.gt.0)then
j3=qstdq(s,j1,j2,inty%s)
Q_ERRT
if(j3.eq.0)then
it=strty%sqs
if(ib.gt.stcbs(1))then
call qvaocb(2)
Q_ERRT
ib=ib+2
do i2=ib,j2+3,-1
stcb(i2:i2)=stcb(i2-2:i2-2)
end do
stcb(j2+2:j2+2)=achar(asq)
do i2=j2+1,j1+1,-1
stcb(i2:i2)=stcb(i2-1:i2-1)
end do
stcb(j1:j1)=achar(asq)
j2=j2+2
i1=i1+2
end if
end if
end if
end if
else
if((j1.lt.j2).and.&
((iachar(s(j2:j2)).eq.aminus).or.&
(iachar(s(j2:j2)).eq.aplus)))then
j3=qstdz(s,j1,j1,inty%s)
Q_ERRT
if(j3.ne.0)then
j3=qstdz(s,j1,j2-1,inty%s)
Q_ERRT
if(j3.ne.0)then
it=strty%ns
end if
end if
if(it.eq.0)then
ier=1
exit
end if
end if
end if
end if
end if
end if
strs=strs+3
call qvaojb(strs)
Q_ERRT
st0=stjbs+strs
stjb(st0-2)=it
stjb(st0-1)=j1
stjb(st0)=j2
stjb(s0)=stjb(s0)+1
j1=0
j2=0
end if
if((icc.ne.aspc).and.&
(icc.ne.alf))then
strs=strs+3
call qvaojb(strs)
Q_ERRT
st0=stjbs+strs
stjb(st0-2)=strty%p
stjb(st0-1)=icc
stjb(st0)=i1
stjb(s0)=stjb(s0)+1
end if
end if
else
if(splic.ne.0)then
if(ic.eq.asq)then
bplic=1-bplic
end if
else if(dplic.ne.0)then
if(ic.eq.adq)then
bplic=1-bplic
end if
end if
j2=i1
end if
end do
if(abs(bplic)+abs(splic)+abs(dplic).ne.0)then
ier=1
end if
if(ier.ne.0)then
stjb(stjbs+1)=-1
else
call qaojb(strs)
Q_ERRT
end if
99 continue
return
end subroutine qnapa
subroutine qmatcha(jk1,jk2,sm)
use,non_intrinsic::qaski
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jk1,jk2
character(kind=asciik,len=smat0),intent(in)::sm
integer(kind=c_int_least32_t),parameter::dpqs(1:10)=[100,112,113,115,40,92,41,91,124,93]
integer(kind=c_int_least32_t),parameter::jdpqs(0:10)=[0,3,3,0,3,0,0,0,0,0,0]
integer(kind=c_int_least32_t),parameter::kdpqs(1:10)=[2,2,1,2,1,1,1,1,1,1]
integer(kind=c_int_least32_t),parameter::istz(1:9)=[105,115,116,122,42,43,45,49,50]
integer(kind=c_int_least32_t)::qstak(0:17)
integer(kind=c_int_least32_t)::ic1,ic2,i1,j0,j1,j2,j3,jks,ll,mf,pf,qs
ll=0
do while(ll.lt.smat0)
ll=ll+1
if(sm(ll:ll).eq.achar(anull))then
ll=ll-1
exit
end if
end do
if((ll.eq.0).or.&
(ll.ge.smat0))then
qerrmsg(1:srec)='qmatcha_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
jbco(0)=0
qstak(:)=0
qs=0
mf=0
pf=0
i1=1
j0=0
j1=0
if(jk1.lt.jk2)then
jks=1
else
jks=-1
end if
d01: do while(i1.le.ll)
ic1=iachar(sm(i1:i1))
j1=0
j2=0
do while(j2.lt.size(dpqs))
j2=j2+1
if(ic1.eq.dpqs(j2))then
j1=j2
exit
end if
end do
if((j1.le.0).or.&
(ll-i1.lt.kdpqs(j1)-1))then
pf=1
exit d01
end if
if(qs.eq.0)then
mf=qstak(0)
else
mf=max(qstak(qs-7),qstak(qs-6))
end if
if(mf.eq.0)then
j2=jdpqs(j1)
if(j2.ne.0)then
if(j0.gt.0)then
j0=j0+jks*j2
else
j0=jk1
end if
end if
if(jks*j0.gt.jks*jk2)then
if(qs.eq.0)then
qstak(0)=1
else
qstak(qs-7)=1
end if
mf=1
end if
end if
select case(j1)
case(1)
ic2=iachar(sm(i1+1:i1+1))
if(ic2.eq.acol)then
if(mf.eq.0)then
if(stjb(j0).ne.strty%p)then
mf=1
else if(stjb(j0+1).ne.dcol)then
mf=1
end if
end if
else if(ic2.eq.ascol)then
if(mf.eq.0)then
if(stjb(j0).ne.strty%p)then
mf=1
else if(stjb(j0+1).ne.dscol)then
mf=1
end if
end if
else if(ic2.eq.aslash)then
if(mf.eq.0)then
if(stjb(j0).ne.strty%p)then
mf=1
else if(stjb(j0+1).ne.dslash)then
mf=1
end if
end if
else if(ic2.eq.istz(3))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%p)then
mf=1
else
jbco(0)=jbco(0)+1
if(jbco(0).ge.size(jbco))then
pf=1
exit d01
end if
jbco(jbco(0))=stjb(j0+1)
end if
end if
else
pf=1
exit d01
end if
case(2)
ic2=iachar(sm(i1+1:i1+1))
if(stib(punct1(0)+ic2).gt.0)then
if(mf.eq.0)then
if(stjb(j0).ne.strty%p)then
mf=1
else if(stjb(j0+1).ne.ic2)then
mf=1
end if
end if
else if(ic2.eq.istz(3))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%p)then
mf=1
else
jbco(0)=jbco(0)+1
if(jbco(0).ge.size(jbco))then
pf=1
exit d01
end if
jbco(jbco(0))=stjb(j0+1)
end if
end if
else if(ic2.ne.aast)then
pf=1
exit d01
end if
case(3)
if(qs.eq.0)then
i1=ll+1
j0=jk2
else
pf=1
end if
exit d01
case(4)
if(mf.eq.0)then
if(stjb(j0).eq.0)then
mf=1
else if(stjb(j0).eq.strty%p)then
mf=1
else if(stjb(j0).eq.strty%dqs)then
mf=1
end if
end if
ic2=iachar(sm(i1+1:i1+1))
if(ic2.eq.istz(1))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%id)then
mf=1
end if
end if
else if(ic2.eq.istz(2))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%sqs)then
mf=1
end if
end if
else if(ic2.eq.istz(3))then
if(mf.eq.0)then
jbco(0)=jbco(0)+1
if(jbco(0).ge.size(jbco))then
pf=1
exit d01
end if
jbco(jbco(0))=stjb(j0)
end if
else if(ic2.eq.istz(4))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%z)then
mf=1
end if
end if
else if(ic2.eq.istz(5))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%ast)then
mf=1
end if
end if
else if(ic2.eq.istz(6))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%plus)then
mf=1
end if
end if
else if(ic2.eq.istz(7))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%minus)then
mf=1
end if
end if
else if(ic2.eq.istz(8))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%id)then
if(stjb(j0).ne.strty%sqs)then
if(stjb(j0).ne.strty%z)then
if(stjb(j0).ne.strty%q)then
mf=1
end if
end if
end if
end if
end if
else if(ic2.eq.istz(9))then
if(mf.eq.0)then
if(stjb(j0).ne.strty%ns)then
mf=1
end if
end if
else
pf=1
exit d01
end if
case(5)
qs=qs+qmatc%ls
jbco(0)=jbco(0)+2
if((qs.ge.size(qstak)).or.&
(jbco(0).ge.size(jbco)))then
pf=1
exit d01
end if
jbco(jbco(0)-1)=qmatc%lc
jbco(jbco(0))=0
qstak(qs-8)=0
qstak(qs-7)=0
qstak(qs-6)=mf
qstak(qs-5)=0
qstak(qs-4)=i1
qstak(qs-3)=j0
qstak(qs-2)=jbco(0)
qstak(qs-1)=jbco(0)
qstak(qs)=qmatc%lc
case(6)
j2=0
if(qs.lt.qmatc%ls)then
j2=1
else if((qstak(qs).ne.qmatc%lc).or.&
(qstak(qs-5).gt.1).or.&
(i1-1.le.qstak(qs-4)))then
j2=1
end if
if(j2.ne.0)then
pf=1
exit d01
end if
j2=qstak(qs-5)
if(mf.eq.0)then
if(j2.eq.0)then
qstak(qs-8)=-(j0+1)
else
qstak(qs-8)=1
qstak(qs-3)=j0
qstak(qs-1)=jbco(0)
j3=qstak(qs-2)
jbco(j3)=jbco(j3)+1
mf=1
end if
else if(j2.gt.0)then
if(qstak(qs-8).lt.0)then
j0=-(qstak(qs-8)+1)
qstak(qs-7)=0
qstak(qs-8)=0
mf=0
end if
end if
qstak(qs-5)=j2+1
case(7)
j2=0
if(qs.lt.qmatc%ls)then
j2=1
else if((qstak(qs).ne.qmatc%lc).or.&
(qstak(qs-5).eq.1).or.&
(qstak(qs-5).gt.2).or.&
(i1-1.le.qstak(qs-4)))then
j2=1
end if
if(j2.ne.0)then
pf=1
exit d01
end if
if(mf.eq.0)then
j2=qstak(qs-2)
jbco(j2)=jbco(j2)+1
if(qstak(qs-5).ne.1)then
i1=qstak(qs-4)
qstak(qs-3)=j0
qstak(qs-1)=jbco(0)
qstak(qs-5)=0
else
mf=1
end if
end if
if(mf.ne.0)then
j0=qstak(qs-3)
jbco(0)=qstak(qs-1)
qs=qs-qmatc%ls
mf=0
end if
case(8)
qs=qs+qmatc%os
jbco(0)=jbco(0)+2
if((qs.ge.size(qstak)).or.&
(jbco(0).ge.size(jbco)))then
pf=1
exit d01
end if
jbco(jbco(0)-1)=qmatc%oc
jbco(jbco(0))=0
qstak(qs-7)=0
qstak(qs-6)=mf
qstak(qs-5)=0
qstak(qs-4)=i1
qstak(qs-3)=j0
qstak(qs-2)=jbco(0)
qstak(qs-1)=jbco(0)
qstak(qs)=qmatc%oc
case(9:10)
j2=0
if(qs.lt.qmatc%os)then
j2=1
else if(qstak(qs).ne.qmatc%oc)then
j2=1
else if(j1.eq.9)then
if(i1-1.le.qstak(qs-4))then
j2=1
end if
else
if(qstak(qs-5).eq.0)then
j2=1
end if
end if
if(j2.ne.0)then
pf=1
exit d01
end if
qstak(qs-5)=qstak(qs-5)+1
j2=qstak(qs-2)
if(mf.eq.0)then
if(jbco(j2).eq.0)then
qstak(qs-1)=jbco(0)
qstak(qs-3)=j0
jbco(j2)=qstak(qs-5)
mf=1
end if
end if
if(j1.eq.9)then
qstak(qs-4)=i1
if(jbco(j2).eq.0)then
qstak(qs-7)=0
j0=qstak(qs-3)
mf=0
end if
else
jbco(0)=qstak(qs-1)
qs=qs-qmatc%os
if(jbco(j2).eq.0)then
mf=1
else
mf=0
end if
end if
case default
pf=1
exit d01
end select
if(mf.ne.0)then
if(qs.eq.0)then
qstak(0)=1
else
qstak(qs-7)=mf
end if
end if
if(qstak(0).ne.0)then
exit d01
end if
i1=i1+kdpqs(j1)
end do d01
if(pf.ne.0)then
qerrmsg(1:srec)='qmatcha_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(qs.ne.0)then
jbco(0)=-1
else if(qstak(0).ne.0)then
jbco(0)=-1
else if(i1-1.ne.ll)then
jbco(0)=-1
else if(j0.ne.jk2)then
jbco(0)=-1
else if(jbco(0).lt.size(jbco))then
jbco(jbco(0)+1)=eoa
end if
99 continue
return
end subroutine qmatcha
subroutine qhsort(ia,ib)
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib
integer(kind=c_int_least32_t)::i0,hi,hj,hl,hr,xtmp
if((ia.le.0).or.&
(ia.gt.ib))then
qerrmsg(1:srec)='qhsort_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
else if(ia.eq.ib)then
go to 99
end if
i0=ia-1
hr=ib-i0
hl=(hr/2)+1
20 continue
if(hl.gt.1)then
hl=hl-1
xtmp=stib(i0+hl)
else
xtmp=stib(i0+hr)
stib(i0+hr)=stib(i0+1)
hr=hr-1
if(hr.eq.1)then
stib(i0+1)=xtmp
go to 99
end if
end if
hj=hl
40 continue
hi=hj
hj=hi+hi
if(hj.le.hr)then
if(hj.lt.hr)then
if(stib(i0+hj).lt.stib(i0+hj+1))then
hj=hj+1
end if
end if
if(xtmp.lt.stib(i0+hj))then
stib(i0+hi)=stib(i0+hj)
go to 40
end if
end if
stib(i0+hi)=xtmp
go to 20
99 continue
return
end subroutine qhsort
subroutine qxipht(ia,ib,ixipht)
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib,ixipht
integer(kind=c_int_least32_t)::ier,jj,i1,j1,j2,j3
ier=0
if(ia.le.0)then
ier=1
else if(ib.le.0)then
ier=1
else if(ib.lt.ia)then
ier=1
else if(ib.gt.stibas(1))then
ier=1
else if(stibs(1).le.0)then
ier=1
else if(stibs(1).ge.stibas(1)-1)then
ier=1
else if(ixipht.lt.0)then
if(ia+ixipht.le.0)then
ier=1
end if
end if
if(ier.ne.0)then
qerrmsg(1:srec)='qxipht_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(ixipht.lt.0)then
j1=ia
j2=ib
j3=1
else if(ixipht.gt.0)then
jj=ixipht-(stibs(1)-ib)
if(jj.gt.0)then
jj=(stibas(1)-ia)-ixipht
if(jj.ge.0)then
qerrmsg(1:srec)='qxipht_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
j1=ib
j2=ia
j3=-1
end if
if(ixipht.ne.0)then
do i1=j1,j2,j3
stib(i1+ixipht)=stib(i1)
end do
end if
99 continue
return
end subroutine qxipht
subroutine qtrm(ia,ib,istib)
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qbprod
integer(kind=c_int_least32_t),intent(in)::ia,ib,istib
integer(kind=c_int_least32_t)::ab,i1,ii,ix,jj,kk,st0,xtmp,ytmp
serrt=qerrty%ok
if(ia.le.0)then
serrt=qerrty%q
else if(ib.le.0)then
serrt=qerrty%q
else if(istib.le.0)then
serrt=qerrty%q
else if((stibas(1)-istib).lt.0)then
serrt=qerrty%q
else
jj=ia
kk=ib
ab=qbprod(jj,kk)
Q_ERRT
st0=istib-(ab-1)
if(st0.le.0)then
serrt=qerrty%q
end if
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qtrm_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
do i1=1,ab-2
ix=0
jj=i1
10 continue
ii=jj/ia
kk=ii+ib*(jj-ii*ia)
if(ix.eq.1)then
ytmp=stib(st0+kk)
stib(st0+kk)=xtmp
xtmp=ytmp
end if
if(kk.gt.i1)then
jj=kk
go to 10
else if(kk.eq.i1)then
if(ix.eq.0)then
if(kk.ne.jj)then
jj=i1
ix=1
xtmp=stib(st0+i1)
go to 10
end if
end if
end if
end do
99 continue
return
end subroutine qtrm
subroutine qios
use,non_intrinsic::qintr,only:jflag
use,non_intrinsic::qkeys,only:jflaty
use,non_intrinsic::qbasic
qerrt(0)=qerrty%os
if(jflag(jflaty%init).eq.0)then
call quput(1)
Q_ERRT
else
call qiomsg(1,0,0,0)
Q_ERRT
end if
99 continue
return
end subroutine qios
subroutine qmas
use,non_intrinsic::qintr,only:jflag
use,non_intrinsic::qkeys,only:jflaty
use,non_intrinsic::qbasic
qerrt(0)=qerrty%os
if(jflag(jflaty%init).eq.0)then
call quput(0)
Q_ERRT
else
call qiomsg(2,0,0,0)
Q_ERRT
end if
99 continue
return
end subroutine qmas
subroutine qrr(ifile,nlin)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon,only:stofc
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ifile
integer(kind=c_int_least32_t),intent(inout)::nlin
integer(kind=c_int_least32_t)::ii,iunit,i1,jj,j1,k1,slin
serrt=qerrty%q
if((ifile.gt.0).and.(ifile.le.mfiles0))then
if(filt(ifile).eq.qfty%ctyp)then
serrt=qerrty%ok
else if(filt(ifile).eq.qfty%mtyp)then
serrt=qerrty%ok
else if(filt(ifile).eq.qfty%styp)then
serrt=qerrty%ok
else if(filt(ifile).eq.qfty%ltyp)then
serrt=qerrty%ok
else if(filt(ifile).eq.qfty%gityp)then
serrt=qerrty%ok
end if
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qrr_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
recdty(:)=0
iunit=filu(ifile)
read(unit=iunit,fmt='(a)',iostat=ios)stxb(1:srecx)
nlin=nlin+1
if(ios.ne.0)then
if(ios.ne.iostat_end)then
call qios
Q_ERRT
end if
recdty(recty%len)=-1
go to 99
end if
do i1=srecx,srec,-1
if(iachar(stxb(i1:i1)).ne.aspc)then
qerrt(0)=qerrty%inp
call qiomsg(19,nlin,nlin,ifile)
Q_ERRT
end if
end do
slin=0
do i1=srec-1,1,-1
jj=iachar(stxb(i1:i1))
if(jj.ne.aspc)then
slin=i1
exit
end if
end do
k1=0
if(nlin.eq.1)then
if(slin.gt.2)then
if(ichar(stxb(1:1)).eq.ubom(1))then
if(ichar(stxb(2:2)).eq.ubom(2))then
if(ichar(stxb(3:3)).eq.ubom(3))then
k1=3
slin=slin-k1
if(qxmod.ne.qmod%api)then
if(ifile.eq.1)then
filb(ifile)=1
end if
end if
end if
end if
end if
end if
end if
if(slin.eq.0)then
go to 85
end if
if((filt(ifile).eq.qfty%ctyp).or.&
(filt(ifile).eq.qfty%mtyp))then
serrt=qerrty%ok
j1=iachar(stxb(k1+1:k1+1))
if(acf(j1).eq.chty%annot)then
if(j1.eq.aast)then
if(qxmod.eq.qmod%fcon)then
if(stofc.gt.0)then
recdty(recty%annot)=1
end if
else
qerrt(0)=qerrty%inp
call qiomsg(14,nlin,nlin,ifile)
Q_ERRT
end if
else
recdty(recty%annot)=1
end if
if(fila(ifile).eq.0)then
fila(ifile)=j1
else if(fila(ifile).ne.j1)then
if((qxmod.ne.qmod%fcon).or.&
(stofc.lt.0))then
qerrt(0)=qerrty%inp
call qiomsg(16,nlin,nlin,ifile)
Q_ERRT
end if
end if
else
j1=iachar(stxb(slin:slin))
if((j1.eq.abslash).or.&
(j1.eq.ascol).or.&
(j1.eq.arsbr))then
recdty(recty%tail)=j1
end if
end if
if(slin.ge.srec0)then
if(filw(ifile).lt.0)then
serrt=qerrty%inp
else
filw(ifile)=1
end if
end if
if(recdty(recty%annot).eq.0)then
if(recdty(recty%tail).eq.abslash)then
if(filc(ifile).lt.0)then
serrt=qerrty%inp
else if(filw(ifile).lt.0)then
serrt=qerrty%inp
else
filc(ifile)=1
end if
else
if(filt(ifile).eq.qfty%ctyp)then
j1=ascol
else if(filt(ifile).eq.qfty%mtyp)then
j1=arsbr
else
j1=-1
end if
if(recdty(recty%tail).ne.j1)then
if(filc(ifile).gt.0)then
serrt=qerrty%inp
else if(filw(ifile).gt.0)then
serrt=qerrty%inp
else
filc(ifile)=-1
filw(ifile)=-1
end if
end if
end if
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(19,nlin,nlin,ifile)
Q_ERRT
end if
end if
if(qxmod.eq.qmod%fcon)then
if(slin.gt.0)then
if(stofc.gt.0)then
if(slin.ge.srec0)then
serrt=qerrty%inp
else if(recdty(recty%annot).eq.0)then
if(iachar(stxb(slin:slin)).eq.abslash)then
if(filt(ifile).ne.qfty%styp)then
serrt=qerrty%inp
end if
end if
end if
else if(stofc.lt.0)then
if(recdty(recty%annot).eq.0)then
if(iachar(stxb(slin:slin)).ne.abslash)then
if(filt(ifile).eq.qfty%ctyp)then
if(iachar(stxb(slin:slin)).ne.ascol)then
serrt=qerrty%inp
end if
end if
if(filt(ifile).eq.qfty%mtyp)then
if(iachar(stxb(slin:slin)).ne.arsbr)then
serrt=qerrty%inp
end if
end if
end if
end if
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(19,nlin,nlin,ifile)
Q_ERRT
end if
end if
end if
do i1=k1+1,k1+slin
j1=iachar(stxb(i1:i1))
if((j1.lt.abo(1)).or.&
(j1.gt.abo(2)))then
if(j1.eq.atab)then
recdty(recty%xchar)=1
else if(j1.gt.127)then
recdty(recty%xchar)=1
else
recdty(recty%fchar)=1
end if
end if
end do
if(recdty(recty%fchar).ne.0)then
serrt=qerrty%inp
else if(recdty(recty%xchar).ne.0)then
if(cflag(confi%xchar).lt.0)then
serrt=qerrty%inp
else if(recdty(recty%annot).eq.0)then
if(filt(ifile).ne.qfty%styp)then
serrt=qerrty%inp
end if
end if
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(17,nlin,nlin,ifile)
Q_ERRT
end if
85 continue
ii=slin+1
call qvaocb(ii)
Q_ERRT
stcb(stcbs(1)+1:stcbs(1)+ii)=stxb(k1+1:k1+slin)//achar(alf)
recdty(recty%len)=slin
99 continue
return
end subroutine qrr
subroutine qdwout(ounit,xw,xt)
use,non_intrinsic::qaski
use,non_intrinsic::qintr
use,non_intrinsic::qbasic
use,non_intrinsic::qfiles,only:non_unit
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ounit,xw,xt
integer(kind=c_int_least32_t),parameter::maxgap=2
integer(kind=c_int_least32_t)::xtab,rtab,tofile
integer(kind=c_int_least32_t)::i1,j1,j2,j3,j4
if(abs(2*xt-xw).gt.xw)then
xtab=(xw/2)+2
else
xtab=xt+2
end if
tofile=0
if(ounit.ne.output_unit)then
if(ounit.ne.error_unit)then
if(ounit.ne.non_unit)then
tofile=1
end if
end if
end if
if(ounit.eq.error_unit)then
flush(unit=output_unit)
end if
if((cflag(confi%dspl).gt.dsplmod%noinfo).or.&
(qerrt(0).gt.qerrty%ale))then
if((qxmod.ne.qmod%api).or.&
(cflag(confi%dspl).eq.dsplmod%dbg))then
j2=len(dmsg)
do i1=1,j2
if(iachar(dmsg(i1:i1)).eq.anull)then
j2=i1-1
exit
end if
end do
if(j2.eq.0)then
if(tofile.eq.0)then
if(jflag(jflaty%sclf).lt.maxgap)then
write(unit=ounit,fmt='(a)')
jflag(jflaty%sclf)=jflag(jflaty%sclf)+1
end if
end if
else
i1=0
rtab=2
j1=0
j3=0
do while(i1.lt.j2)
i1=i1+1
j4=iachar(dmsg(i1:i1))
if(j4.eq.aspc)then
if(i1.eq.1)then
j3=i1
else if(iachar(dmsg(i1-1:i1-1)).ne.aspc)then
j3=i1
end if
end if
if(j4.eq.alf)then
if(i1.gt.j1+1)then
write(unit=ounit,fmt='(a)',iostat=ios)dmsg(j1+1:i1-1)
if(tofile.eq.0)then
jflag(jflaty%sclf)=0
else
if(ios.ne.0)then
call qios
Q_ERRT
end if
end if
else if(jflag(jflaty%sclf).lt.maxgap)then
if(tofile.eq.0)then
write(unit=ounit,fmt='(a)')
jflag(jflaty%sclf)=jflag(jflaty%sclf)+1
end if
end if
if(i1.eq.j2)then
if(jflag(jflaty%sclf).lt.maxgap)then
if(tofile.eq.0)then
write(unit=ounit,fmt='(a)')
jflag(jflaty%sclf)=jflag(jflaty%sclf)+1
end if
end if
end if
rtab=2
j1=i1
else if(i1.eq.j2)then
write(unit=ounit,fmt='(a)',iostat=ios)dmsg(j1+1:j2)
if(tofile.eq.0)then
jflag(jflaty%sclf)=0
else
if(ios.ne.0)then
call qios
Q_ERRT
end if
end if
if(j4.eq.alf)then
if(jflag(jflaty%sclf).lt.maxgap)then
if(tofile.eq.0)then
write(unit=ounit,fmt='(a)')
jflag(jflaty%sclf)=jflag(jflaty%sclf)+1
end if
end if
end if
else if(i1-j1.gt.xw-rtab)then
if(j3-j1.gt.1)then
write(unit=ounit,fmt='(a,/,a)',advance='no',iostat=ios)dmsg(j1+1:j3-1),blak(1:xtab)
if(tofile.eq.0)then
jflag(jflaty%sclf)=0
else
if(ios.ne.0)then
call qios
Q_ERRT
end if
end if
rtab=2+xtab
j1=j3
end if
end if
end do
end if
if(ounit.eq.error_unit)then
flush(unit=error_unit)
else if(tofile.ne.0)then
if(cflag(confi%flsh).ne.0)then
flush(unit=ounit,iostat=ios)
if(ios.ne.0)then
call qios
Q_ERRT
end if
end if
end if
end if
end if
99 continue
return
end subroutine qdwout
subroutine qout(junit)
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::junit
integer(kind=c_int_least32_t)::f1,i1,j1,j2,j3,j4,iunit
f1=filo(junit)
j1=stwbpf(f1)+1
j2=stwbqf(f1)
serrt=qerrty%ok
if(j1.le.0)then
serrt=qerrty%q
else if(j2.lt.j1)then
serrt=qerrty%q
else if(len(stwb).le.j2)then
serrt=qerrty%q
else if(iachar(stwb(j2:j2)).ne.alf)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qout_2'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
iunit=filu(junit)
if(filt(junit).eq.qfty%ptyp)then
qerrmsg(1:srec)='qout_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(cflag(confi%nontlf).eq.0)then
if(cflag(confi%lf).ne.0)then
if(j1.lt.j2)then
write(unit=iunit,fmt='(a)',iostat=ios)stwb(j1:j2-1)
else
write(unit=iunit,fmt='(a)',iostat=ios)
end if
else
j3=j1
do i1=j1,j2
if(iachar(stwb(i1:i1)).eq.alf)then
if(j3.lt.i1)then
write(unit=iunit,fmt='(a)',iostat=ios)stwb(j3:i1-1)
else
write(unit=iunit,fmt='(a)',iostat=ios)
end if
if(ios.ne.0)then
exit
end if
j3=i1+1
end if
end do
end if
else
if(cflag(confi%lf).eq.0)then
j4=j1-1
do i1=j2-1,j1,-1
if(iachar(stwb(i1:i1)).ne.alf)then
j4=i1
exit
end if
end do
j3=j1
do i1=j1,j4+1
if(iachar(stwb(i1:i1)).eq.alf)then
if(j3.lt.i1)then
write(unit=iunit,fmt='(a)',advance='no',iostat=ios)stwb(j3:i1-1)
if(ios.ne.0)then
exit
end if
end if
j3=i1+1
end if
end do
if(ios.eq.0)then
do i1=j4+1,j2
write(unit=iunit,fmt='(a)',iostat=ios)
if(ios.ne.0)then
exit
end if
end do
end if
else
j3=j1-1
j4=j1-1
do i1=j1,j2
if(iachar(stwb(i1:i1)).ne.alf)then
j4=j4+1
stwb(j4:j4)=stwb(i1:i1)
j3=i1
end if
end do
do i1=j3+1,j2-1
j4=j4+1
stwb(j4:j4)=stwb(i1:i1)
end do
if(j1.le.j4)then
write(unit=iunit,fmt='(a)',iostat=ios)stwb(j1:j4)
end if
end if
end if
if(ios.ne.0)then
call qios
Q_ERRT
end if
99 continue
return
end subroutine qout
subroutine qopen(junit)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::junit
integer(kind=c_int_least32_t)::ii,j1,j2,j3,j4,jd1,jd2,delty,iunit,ite
logical::lun=.true.
logical::loun=.true.
serrt=qerrty%ok
if(junit.le.0)then
serrt=qerrty%q
else if(junit.gt.mfiles0)then
serrt=qerrty%q
else if(filp(junit).eq.nap)then
serrt=qerrty%q
else if(filu(junit).ne.non_unit)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qopen_1'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
j3=filp(junit)
j4=filq(junit)
delty=-1
jd1=0
jd2=0
if((filt(junit).eq.qfty%otyp).or.&
(filt(junit).eq.qfty%wtyp))then
delty=0
if(udirpq(udir%odirp).ne.nap)then
if(cflag(confi%del).gt.0)then
delty=1
end if
jd1=udir%odirp
jd2=udir%odirq
end if
else if(filt(junit).eq.qfty%styp)then
if(udirpq(udir%sdirp).ne.nap)then
jd1=udir%sdirp
jd2=udir%sdirq
end if
else if(filt(junit).eq.qfty%mtyp)then
if(udirpq(udir%mdirp).ne.nap)then
jd1=udir%mdirp
jd2=udir%mdirq
end if
else if(filt(junit).eq.qfty%gotyp)then
delty=1
end if
if(jd1.eq.0)then
j1=j3
j2=j4
else
if(cflag(confi%psep).eq.0)then
qerrmsg(1:srec)='qclose_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
j1=stcbs(1)+1
ii=(j4-j3)+(udirpq(jd2)-udirpq(jd1))+4
call qaocb(ii)
Q_ERRT
j2=stcbs(1)-1
stcb(j1:stcbs(1))=stcb(udirpq(jd1):udirpq(jd2))//achar(p_sep)//stcb(j3:j4)//char(anull)
jd1=ii
end if
ite=0
10 continue
inquire(file=stcb(j1:j2),exist=lun,opened=loun,iostat=ios)
if(ios.ne.0)then
call qios
Q_ERRT
else if(loun)then
qerrt(0)=qerrty%inp
call qiomsg(7,0,0,junit)
Q_ERRT
else if(delty.lt.0)then
if(.not.lun)then
qerrt(0)=qerrty%inp
call qiomsg(12,0,0,junit)
Q_ERRT
end if
else if(lun)then
ii=-1
if(delty.gt.0)then
if(ite.eq.0)then
call qfdel(j1,j2,ii)
Q_ERRT
if(ii.ne.0)then
ite=ite+1
go to 10
end if
end if
end if
if(ii.lt.0)then
qerrt(0)=qerrty%inp
call qiomsg(8,0,0,junit)
Q_ERRT
else
qerrt(0)=qerrty%inp
call qiomsg(9,0,0,junit)
Q_ERRT
end if
end if
if(delty.lt.0)then
open(access='sequential',action='read',file=stcb(j1:j2),iostat=ios,newunit=iunit,pad='yes',&
position='rewind',status='old')
else
open(access='sequential',action='write',file=stcb(j1:j2),iostat=ios,newunit=iunit,status='new')
end if
if(ios.ne.0)then
filu(junit)=non_unit
qerrt(0)=qerrty%os
call qiomsg(9,0,0,junit)
Q_ERRT
end if
filu(junit)=iunit
if(delty.ge.0)then
if(cflag(confi%bom).gt.0)then
write(unit=iunit,fmt='(a)',advance='no',iostat=ios)char(ubom(1))//char(ubom(2))//char(ubom(3))
if(ios.ne.0)then
call qios
Q_ERRT
end if
filb(junit)=1
end if
if(filt(junit).eq.qfty%wtyp)then
write(unit=iunit,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
Q_ERRT
end if
dmsg(1:sdrec)=sthb2(2:sdrec)//achar(anull)
call qdwout(iunit,sdrec,0)
Q_ERRT
end if
end if
99 continue
return
end subroutine qopen
subroutine qfdel(j1,j2,jj)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qintr
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::j1,j2
integer(kind=c_int_least32_t),intent(out)::jj
integer(kind=c_int_least32_t)::iunit
if(cflag(confi%del).eq.0)then
jj=1
else
jj=0
open(access='sequential',action='readwrite',file=stcb(j1:j2),iostat=ios,newunit=iunit,status='old')
if(ios.ne.0)then
qerrt(0)=qerrty%os
call qiomsg(9,0,0,iunit)
Q_ERRT
else
close(unit=iunit,status='delete',iostat=ios)
if(ios.eq.0)then
jj=1
else
qerrt(0)=qerrty%os
call qiomsg(11,0,0,iunit)
Q_ERRT
end if
end if
end if
99 continue
return
end subroutine qfdel
subroutine qopd(j1,j2,jj)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qintr
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::j1,j2
integer(kind=c_int_least32_t),intent(inout)::jj
integer(kind=c_int_least32_t)::ier,iunit,slen,ii,i1,j3,j4
j3=j1
do i1=j2,j1,-1
j4=iachar(stcb(i1:i1))
if((j4.eq.aslash).or.&
(j4.eq.abslash).or.&
(j4.eq.acol))then
j3=i1+1
exit
end if
end do
j4=qtfpq-qtfpp
ier=0
if(j2-j3.le.j4)then
ier=1
else if(stcb(j3:j3+j4).ne.stcb(qtfpp:qtfpq))then
ier=1
end if
if(ier.ne.0)then
go to 99
end if
open(access='sequential',action='read',file=stcb(j1:j2),iostat=ios,newunit=iunit,pad='yes',&
position='rewind',status='old')
if(ios.ne.0)then
qerrt(0)=qerrty%os
close(unit=iunit,status='keep')
go to 99
end if
read(unit=iunit,fmt='(a)',iostat=ios)stxb(1:srec)
jj=0
if(ios.ne.0)then
if(ios.ne.iostat_end)then
qerrt(0)=qerrty%os
close(unit=iunit,status='keep')
go to 99
else
jj=1
end if
end if
if(jj.eq.0)then
slen=0
do i1=srec,1,-1
if(iachar(stxb(i1:i1)).ne.aspc)then
slen=i1
exit
end if
end do
j3=iachar(stcb(qgfmp:qgfmp))
j4=iachar(stcb(qgfmq:qgfmq))
ii=qgfmq-qgfmp
if(slen.lt.ii)then
go to 99
end if
do i1=1,slen-ii
if(iachar(stxb(i1:i1)).eq.j3)then
if(iachar(stxb(i1+ii:i1+ii)).eq.j4)then
if(stxb(i1:i1+ii).eq.stcb(qgfmp:qgfmq))then
jj=1
end if
end if
end if
end do
if(jj.eq.0)then
if(iachar(stcb(qgfmq:qgfmq)).eq.aspc)then
if(stxb(slen-ii+1:slen).eq.stcb(qgfmp:qgfmq-1))then
jj=1
end if
end if
end if
end if
if(jj.ne.0)then
close(unit=iunit,status='delete',iostat=ios)
if(ios.ne.0)then
qerrt(0)=qerrty%os
go to 99
end if
end if
99 continue
return
end subroutine qopd
subroutine qclose(junit)
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::junit
logical::lun=.true.
character(kind=asciik,len=6)::fstat
integer(kind=c_int_least32_t)::i1,jj,j1,j2,iunit
if(qerrt(0).eq.qerrty%os)then
go to 99
end if
serrt=qerrty%ok
if(junit.lt.0)then
serrt=qerrty%q
else if(junit.gt.mfiles0)then
serrt=qerrty%q
else if(junit.ne.0)then
if(filt(junit).eq.qfty%ptyp)then
serrt=qerrty%q
end if
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qclose_2'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
if(junit.eq.0)then
j1=1
j2=mfiles0
else
j1=junit
j2=junit
end if
do i1=j1,j2
iunit=filu(i1)
if((iunit.ne.non_unit).and.&
(filt(i1).ne.0).and.&
(filt(i1).ne.qfty%ptyp))then
inquire(unit=iunit,opened=lun,iostat=ios)
if((ios.eq.0).and.&
(lun))then
jj=0
if(filt(i1).eq.qfty%otyp)then
if(qerrt(0).gt.qerrty%ale)then
jj=1
end if
else if(filt(i1).eq.qfty%wtyp)then
if(jflag(jflaty%nwf).gt.0)then
write(unit=iunit,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
Q_ERRT
end if
else
jj=1
end if
else if(filt(i1).eq.qfty%gotyp)then
if(qerrt(0).gt.qerrty%ale)then
jj=1
end if
end if
if(jj.eq.0)then
jj=4
fstat(1:jj)='keep'
else
serrt=qerrty%ok
if(filt(i1).ne.qfty%wtyp)then
if(filt(i1).ne.qfty%otyp)then
if(filt(i1).ne.qfty%gotyp)then
serrt=qerrty%q
end if
end if
end if
if(fild(i1).ne.qfdty%dok)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qclose_3'//achar(anull)
qerrt(0)=serrt
call qmput(0,0,0)
Q_ERRT
end if
jj=6
fstat(1:jj)='delete'
end if
if(cflag(confi%flsh).ne.0)then
if(filt(i1).eq.qfty%otyp)then
flush(unit=iunit,iostat=ios)
if(ios.ne.0)then
call qios
Q_ERRT
end if
end if
end if
close(unit=iunit,status=fstat(1:jj),iostat=ios)
filu(i1)=non_unit
filp(i1)=nap
filq(i1)=nap
filt(i1)=0
fild(i1)=qfdty%dno
end if
if(ios.ne.0)then
call qios
Q_ERRT
end if
end if
end do
99 continue
return
end subroutine qclose
subroutine qrstc(enstm,enlin,edbl,ja,jb)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(inout)::enstm,edbl,enlin,ja,jb
integer(kind=c_int_least32_t),parameter::datls=5
integer(kind=c_int_least32_t)::dbl,stloop,ier,ifile,instm,nlin,nstm,p1,p2,slin,tsl
integer(kind=c_int_least32_t)::i1,ii,j1,j2,j3
if(enstm.eq.1)then
ifile=0
do i1=1,nfiles
if(filt(i1).eq.qfty%ctyp)then
ifile=i1
call qopen(ifile)
Q_ERRT
exit
end if
end do
ndrec=0
nstm=0
nlin=0
rlink=nap
p1=nap
p2=nap
end if
instm=0
tsl=0
dbl=0
stloop=0
ier=0
do while(stloop.eq.0)
call qrr(ifile,nlin)
Q_ERRT
slin=recdty(recty%len)
if(slin.lt.0)then
if(instm.ne.0)then
ier=1
end if
exit
end if
if(instm.ne.0)then
if(slin.eq.0)then
ier=1
else if(recdty(recty%annot).ne.0)then
ier=1
end if
if(ier.ne.0)then
exit
end if
else
if(slin.eq.0)then
cycle
else if(recdty(recty%annot).ne.0)then
cycle
end if
end if
if((slin.ge.srec0).or.&
(recdty(recty%tail).eq.abslash))then
if(filw(ifile).eq.0)then
filw(ifile)=1
else if(filw(ifile).lt.0)then
ier=1
exit
end if
else if(recdty(recty%annot).eq.0)then
if(recdty(recty%tail).ne.ascol)then
if(filw(ifile).eq.0)then
filw(ifile)=-1
else if(filw(ifile).gt.0)then
ier=1
exit
end if
end if
end if
if(recdty(recty%tail).eq.abslash)then
j1=0
do i1=stcbs(1)+slin-1,stcbs(1)+1,-1
j2=iachar(stcb(i1:i1))
if(j2.ne.aspc)then
j1=stcbs(1)+slin-i1
slin=slin-j1
exit
end if
end do
if(j1.eq.0)then
ier=1
exit
end if
end if
if(slin.eq.0)then
if(instm.ne.0)then
ier=1
exit
end if
cycle
end if
if(instm.eq.0)then
dbl=nlin
end if
if(recdty(recty%tail).eq.abslash)then
instm=1
else if(recdty(recty%tail).eq.ascol)then
instm=0
nstm=nstm+1
stloop=1
else
instm=1
end if
if(qxmod.ne.qmod%fcon)then
if(filw(ifile).lt.0)then
qerrt(0)=qerrty%inp
call qiomsg(14,dbl,nlin,ifile)
Q_ERRT
end if
end if
tsl=tsl+slin+1
if(tsl.gt.sxbuff0)then
qerrt(0)=qerrty%inp
call qcfmsg0(2,0,0)
Q_ERRT
end if
call qaocb(slin+1)
Q_ERRT
stcb(stcbs(1):stcbs(1))=achar(alf)
ndrec=ndrec+1
call qlink(p2,datls)
Q_ERRT
if(rlink.eq.nap)then
rlink=p2
end if
stib(p2+1)=stcbs(1)-slin
stib(p2+2)=slin+1
stib(p2+3)=nlin
stib(p2+4)=nlin-dbl
stib(p2+5)=ndrec
end do
if(ier.ne.0)then
go to 80
end if
call qaocb(1)
Q_ERRT
stcb(stcbs(1):stcbs(1))=achar(anull)
if(slin.lt.0)then
ii=nstm+1
irecc(0)=stibs(1)
call qaoib(2*ii)
Q_ERRT
frecc(0)=irecc(0)+ii
stib(frecc(0))=eoa
stib(stibs(1))=eoa
j1=0
j2=0
p2=rlink
do while(j1.lt.ndrec)
j1=j1+1
if(stib(p2+4).eq.0)then
if(j2.gt.0)then
stib(frecc(0)+j2)=j1-1
end if
j2=j2+1
stib(irecc(0)+j2)=j1
end if
p2=stib(p2)
end do
if((j1.ne.ndrec).or.&
(j2.ne.nstm))then
qerrmsg(1:srec)='qrstc_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
stib(frecc(0)+nstm)=ndrec
call qsp(2,0,0)
Q_ERRT
end if
ier=0
if(enstm.le.0)then
ier=1
else if(enstm.gt.nstm)then
enstm=0
end if
if(ier.ne.0)then
qerrmsg(1:srec)='qrstc_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(enstm.gt.0)then
enlin=stib(p2+3)
edbl=enlin-stib(p2+4)
if(p1.eq.nap)then
p1=rlink
else
p1=stib(p1)
end if
ja=stib(p1+1)
jb=(stib(p2+1)-1)+stib(p2+2)
j1=p1
do while(j1.ne.p2)
j2=stib(j1)
ier=0
if(stib(j1+2).ne.stib(j2+1)-stib(j1+1))then
ier=1
end if
j3=(stib(j1+1)-1)+stib(j1+2)
if(j3.ne.stib(j2+1)-1)then
ier=1
else if(iachar(stcb(j3:j3)).ne.alf)then
ier=1
end if
if(ier.ne.0)then
qerrmsg(1:srec)='qrstc_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
j1=j2
end do
else
jb=0
end if
p1=p2
80 continue
if(ier.ne.0)then
qerrt(0)=qerrty%inp
call qcfmsg0(1,dbl,nlin)
Q_ERRT
end if
99 continue
return
end subroutine qrstc
subroutine qinputs
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qsty
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qsigz,qstoz,wtoz,qilsd
integer,parameter::qseps(1:1)=[aslash]
integer(kind=c_int_least32_t),parameter::leftab=2
integer(kind=c_int_least32_t)::ii,ij,ik,i1,i2,i3,i4,jj,jk,j1,j2,j3,j4,j5,kid,kk,ll,ja,jb
integer(kind=c_int_least32_t)::ifile,icom,ier
integer(kind=c_int_least32_t)::atyp,ktyp, nphia,ntf1,tfch,tfcl,tfcn,tfv
integer(kind=c_int_least32_t)::bot,dbl,drlink,nlin,nmp,nmp0,pp0,pp1,pp2,slin,top
integer(kind=c_int_least32_t)::stjr,stjr0,styp
integer(kind=c_int_least32_t)::comt(1:dekc%ubo)
integer(kind=c_int_least32_t)::xli(1:maxleg)
call qinit0
Q_ERRT
if(stjbs.ne.stj0)then
qerrmsg(1:srec)='qinputs_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
inco=0
outg=0
nleg=0
vdpi(0)=nap
vdpj(0)=nap
efinvdc(0)=nap
efm(0)=nap
ntf=0
stjr0=nap
drlink=nap
tftyp(0)=nap
tfnarg(0)=nap
tfa(0)=nap
tfb(0)=nap
tfc(0)=nap
tf2(0)=nap
tfo(0)=nap
tfills(0)=nap
tfiuls(0)=nap
tftb(0)=nap
tfta(0)=nap
tftic(0)=nap
rbri(:)=1
sbri(:)=1
zbri(:)=1
zcho(:)=1
zpro(:)=1
call qaocb(2)
Q_ERRT
ii=stcbs(1)-1
stcb(ii:stcbs(1))=achar(azero)//achar(anull)
momzp(0)=ii
momzq(0)=ii
momzl(0)=1
nmp=0
comc(:)=0
ncom=0
icom=dekc%conf
dbl=0
nlin=0
ifile=0
do i1=1,nfiles
if(filt(i1).eq.qfty%ctyp)then
ifile=i1
exit
end if
end do
03 continue
kk=ncom+1
call qrstc(kk,nlin,dbl,ja,jb)
Q_ERRT
if(kk.ne.0)then
ncom=kk
else
do i1=size(comc),1,-1
if((stib(oisk(0)+i1).eq.stmty%ureq).or.&
(stib(oisk(0)+i1).eq.stmty%dreq))then
if(comc(i1).eq.0)then
qerrt(0)=qerrty%inp
call qcfmsg0(3,0,0)
Q_ERRT
end if
end if
end do
go to 301
end if
slin=jb-ja
bot=ja
top=jb-1
j3=iachar(stcb(top:top))
ier=0
if(ja.gt.jb)then
ier=1
else if(ja.lt.0)then
ier=1
else if(jb.ge.stcbs(1))then
ier=1
else if(iachar(stcb(jb:jb)).ne.alf)then
ier=1
else if(j3.ne.ascol)then
ier=1
end if
if(ier.ne.0)then
go to 80
end if
jj=stibs(1)
stjr=stjbs
if(stjr0.eq.nap)then
stjr0=stjr
end if
top=top+1
call qstap(bot,top,qfty%ctyp)
Q_ERRT
if(stibs(1).ne.jj)then
qerrmsg(1:srec)='qinputs_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ier=0
if(stapi(1).le.0)then
ier=1
else if(stapi(1).gt.size(comc))then
ier=1
else if(stapi(2).lt.0)then
ier=1
end if
pp1=stjr+2
pp2=pp1+3*(stjb(pp1-1)-1)
if(stapi(1).eq.dekc%lib)then
ier=1
end if
if(ier.ne.0)then
go to 80
end if
if(cflag(confi%msg).eq.0)then
if(stapi(1).gt.dekc%msg)then
cflag(confi%msg)=-1
if(stmbs(1).gt.0)then
stmbs(1)=0
deallocate(stmb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
end if
end if
comt(:)=0
do while((icom.ne.stapi(1)).and.&
(comt(icom).eq.0).and.&
((stib(oisk(0)+icom).eq.stmty%uopt).or.&
(stib(oisk(0)+icom).eq.stmty%dopt)))
comt(icom)=1
icom=stib(fisk(0)+icom)
end do
do while((icom.lt.stapi(1)).and.&
((comc(icom).gt.0).or.&
(stib(oisk(0)+icom).eq.stmty%uopt).or.&
(stib(oisk(0)+icom).eq.stmty%dopt)))
icom=icom+1
end do
if(icom.ne.stapi(1))then
go to 80
end if
if(comc(icom).gt.0)then
if((stib(oisk(0)+icom).eq.stmty%uopt).or.&
(stib(oisk(0)+icom).eq.stmty%ureq))then
go to 80
end if
end if
comc(icom)=comc(icom)+1
if(icom.gt.dekc%conf)then
if(nfiles.eq.1)then
if(filb(nfiles).ne.0)then
if(cflag(confi%bom).eq.0)then
cflag(confi%bom)=1
end if
end if
end if
end if
serrt=qerrty%ok
if(icom.eq.dekc%conf)then
if(ncom.ne.1)then
go to 80
end if
cflag(confi%dspl)=dsplmod%dflt
j1=stjb(stjbs-2)+3
do i1=1,stapi(2)
j1=j1+6
ij=0
call qmstr0(stcb,stjb(j1),stjb(j1+1),popt0(0),wopt0(0),aopt0(0),ij)
Q_ERRT
if(ij.le.0)then
go to 80
end if
ik=stib(xopt0(0)+ij)
ij=stib(copt0(0)+ij)
if(ij.le.0)then
qerrmsg(1:srec)='qinputs_6'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(cflag(ij).eq.0)then
cflag(ij)=ik
else
if(cflag(ij).eq.ik)then
qerrt(0)=max(qerrt(0),qerrty%ale)
else
qerrt(0)=max(qerrt(0),qerrty%inp)
end if
end if
if(qerrt(0).ne.qerrty%ok)then
call qcfmsg(2,0,0)
Q_ERRT
end if
end do
if(cflag(confi%dspl).eq.dsplmod%dflt)then
if(qxmod.eq.qmod%api)then
cflag(confi%dspl)=dsplmod%noinfo
else if(cflag(confi%qlist).lt.0)then
cflag(confi%dspl)=dsplmod%vrbs
else
cflag(confi%dspl)=dsplmod%info
end if
end if
if(qerrt(0).ne.qerrty%ok)then
call qcfmsg(2,0,0)
Q_ERRT
end if
else if(icom.eq.dekc%psep)then
ll=0
if(stapi(2).eq.1)then
j1=stjr+9
ll=stjb(j1+1)-1-stjb(j1)
end if
if(ll.gt.0)then
serrt=qerrty%ok
if(ll.ne.1)then
serrt=qerrty%q
else
j2=stjb(j1+1)-1
j2=iachar(stcb(j2:j2))
if(acf(j2).gt.0)then
serrt=qerrty%inp
else if(j2.eq.aspc)then
serrt=qerrty%inp
else if(cflag(confi%psep).ne.0)then
serrt=qerrty%q
else
cflag(confi%psep)=1
p_sep=j2
end if
end if
ii=0
do i1=1,size(qseps)
if(p_sep.eq.qseps(i1))then
ii=1
end if
end do
if(ii.eq.0)then
serrt=qerrty%inp
end if
else
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qcfmsg(4,0,0)
Q_ERRT
end if
else if(icom.eq.dekc%ldir)then
go to 80
else if(icom.eq.dekc%mdir)then
serrt=qerrty%ok
if(stapi(2).eq.1)then
call qsetudir(udir%mdirp,udir%mdirq,stjr,qfty%mdirtyp)
Q_ERRT
else
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
else if(icom.eq.dekc%odir)then
serrt=qerrty%ok
if(stapi(2).eq.1)then
call qsetudir(udir%odirp,udir%odirq,stjr,qfty%odirtyp)
Q_ERRT
else
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
else if(icom.eq.dekc%sdir)then
serrt=qerrty%ok
if(stapi(2).eq.1)then
call qsetudir(udir%sdirp,udir%sdirq,stjr,qfty%sdirtyp)
Q_ERRT
else
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
else if(icom.eq.dekc%msg)then
ll=-1
if(stapi(2).eq.0)then
ll=0
else if(stapi(2).eq.1)then
j1=stjr+9
ll=j1
call qsetfname(qfty%wtyp,stjb(j1),stjb(j1+1),ll)
Q_ERRT
end if
if(ll.gt.0)then
if(cflag(confi%del).ne.0)then
if(udirpq(udir%odirp).eq.nap)then
qerrt(0)=qerrty%inp
call qcfmsg(5,0,0)
Q_ERRT
end if
end if
call qopen(nfiles)
Q_ERRT
if(filu(nfiles).ne.non_unit)then
cflag(confi%msg)=1
if(stmbs(1).gt.1)then
j1=1
do i1=1,stmbs(1)
if(iachar(stmb(i1:i1)).eq.anull)then
ii=min(i1-1,j1+len(dmsg)-1)
dmsg=blak(1:leftab)//stmb(j1:i1-1)//achar(anull)
call qdwout(filu(nfiles),sdrec,leftab)
Q_ERRT
dmsg(1:sdrec)=sthb2(2:sdrec)//achar(anull)
call qdwout(filu(nfiles),sdrec,0)
Q_ERRT
j1=i1+1
end if
end do
stmbs(1)=0
deallocate(stmb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
jflag(jflaty%nwf)=jflag(jflaty%nw)
end if
end if
else
go to 80
end if
end if
if(ncom.eq.1)then
call qsp(0,0,0)
Q_ERRT
end if
if(rlink.eq.nap)then
qerrmsg(1:srec)='qinputs_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
else if(ncom.eq.1)then
drlink=rlink
else
drlink=stib(drlink)
end if
do while(stib(drlink).ge.drlink)
j1=stib(drlink+1)
j2=stib(drlink+2)
call qsp(1,j1,j1+j2-1)
Q_ERRT
if(stib(drlink).ne.drlink)then
drlink=stib(drlink)
else
exit
end if
end do
if((icom.eq.dekc%conf).or.&
(icom.eq.dekc%ldir).or.&
(icom.eq.dekc%mdir).or.&
(icom.eq.dekc%odir).or.&
(icom.eq.dekc%sdir).or.&
(icom.eq.dekc%psep).or.&
(icom.eq.dekc%msg))then
go to 143
else if(icom.eq.dekc%outp)then
go to 102
else if(icom.eq.dekc%sty)then
go to 103
else if(icom.eq.dekc%model)then
go to 104
else if((icom.eq.dekc%in).or.&
(icom.eq.dekc%out))then
go to 106
else if(icom.eq.dekc%loop)then
go to 107
else if(icom.eq.dekc%loopk)then
go to 108
else if(icom.eq.dekc%opt)then
go to 109
else if(icom.eq.dekc%part)then
go to 110
else if(icom.eq.dekc%off)then
go to 111
else if(icom.eq.dekc%maxc)then
go to 112
else if(icom.eq.dekc%zerok)then
go to 113
else if((icom.eq.dekc%tru).or.&
(icom.eq.dekc%fal))then
go to 130
else
go to 80
end if
102 continue
if(qxmod.eq.qmod%api)then
go to 80
end if
if(cflag(confi%del).ne.0)then
if(udirpq(udir%odirp).eq.nap)then
qerrt(0)=qerrty%inp
call qcfmsg(5,0,0)
Q_ERRT
end if
end if
if(dso.eq.0)then
dso=1
if(comc(dekc%outp).ne.1)then
serrt=qerrty%inp
else if(comc(dekc%sty).ne.0)then
serrt=qerrty%inp
end if
else
if(comc(dekc%outp).ne.comc(dekc%sty)+max(0,dso))then
serrt=qerrty%inp
end if
end if
if(qerrt(0).ne.qerrty%ok)then
go to 80
end if
ll=-1
if(stapi(2).eq.0)then
ll=0
else if(stapi(2).eq.1)then
j1=stjr+9
ll=j1
call qsetfname(qfty%otyp,stjb(j1),stjb(j1+1),ll)
Q_ERRT
end if
if(ll.le.0)then
go to 80
end if
go to 143
103 continue
if(nsfiles.ge.sfiles0)then
qerrt(0)=qerrty%inp
call qcfmsg(9,0,0)
Q_ERRT
end if
serrt=qerrty%ok
if(qxmod.eq.qmod%auto)then
if(dso.eq.0)then
dso=-1
if(comc(dekc%outp).ne.0)then
serrt=qerrty%inp
else if(comc(dekc%sty).ne.1)then
serrt=qerrty%inp
end if
else
if(comc(dekc%outp).ne.comc(dekc%sty)+min(0,dso))then
if(comc(dekc%outp).ne.0)then
serrt=qerrty%inp
end if
end if
end if
else if(qxmod.eq.qmod%api)then
dso=1
if(nfiles.lt.mfiles0)then
nfiles=nfiles+1
filt(nfiles)=qfty%ptyp
else
qerrt(0)=qerrty%inp
call qcfmsg(9,0,0)
Q_ERRT
end if
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
ll=-1
if(stapi(2).eq.0)then
ll=0
else if(stapi(2).eq.1)then
j1=stjr+9
ll=j1
call qsetfname(qfty%styp,stjb(j1),stjb(j1+1),ll)
Q_ERRT
end if
if(ll.le.0)then
go to 80
end if
go to 143
104 continue
if(stapi(2).gt.2)then
serrt=qerrty%q
else if(qxmod.eq.qmod%auto)then
if(comc(dekc%outp).ne.comc(dekc%sty))then
if(comc(dekc%outp).ne.0)then
serrt=qerrty%inp
end if
else if(cflag(confi%qlist).gt.0)then
serrt=qerrty%inp
end if
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
if(qxmod.eq.qmod%api)then
cflag(confi%qlist)=1
else if(cflag(confi%qlist).lt.0)then
cflag(confi%qlist)=0
else
do i1=1,nfiles
if(filt(i1).eq.qfty%otyp)then
if(filp(i1).ne.nap)then
cflag(confi%qlist)=1
exit
end if
end if
end do
end if
if(stapi(2).eq.0)then
ll=0
else
j1=pp1+7
if(stapi(2).eq.2)then
smodp(0)=stjb(j1)
smodq(0)=stjb(j1+1)
cflag(confi%subm)=1
j1=j1+6
end if
ll=j1
call qsetfname(qfty%mtyp,stjb(j1),stjb(j1+1),ll)
Q_ERRT
end if
if(ll.le.0)then
go to 80
end if
go to 143
106 continue
nphia=stapi(2)
kk=4
if(icom.eq.dekc%in)then
inco=nphia
leg(0)=stibs(1)+kk
ii=kk*(maxleg+2)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
else
outg=nphia
end if
if(nphia.gt.0)then
if(pp2-pp1.eq.3*(2*nphia+1))then
if(icom.eq.dekc%in)then
cflag(confi%pq)=0
else if(cflag(confi%pq).ne.0)then
go to 80
end if
else if(pp2-pp1.eq.3*(5*nphia+1))then
if(icom.eq.dekc%in)then
cflag(confi%pq)=1
else if(inco.eq.0)then
cflag(confi%pq)=1
else if(cflag(confi%pq).eq.0)then
go to 80
end if
end if
j1=6+9*cflag(confi%pq)
j2=pp1+7-j1
do i1=1,nphia
nleg=nleg+1
if(nleg.gt.maxleg)then
qerrt(0)=qerrty%inp
call qcfmsg(22,0,0)
Q_ERRT
end if
j2=j2+j1
jk=0
call qmstr0(stcb,stjb(j2),stjb(j2+1),namep(0),namel(0),nap,jk)
Q_ERRT
if(jk.eq.0)then
qerrt(0)=qerrty%inp
call qcfmsg(13,0,0)
Q_ERRT
end if
leg(0)=leg(0)+1
if(icom.eq.dekc%in)then
stib(leg(0))=stib(link(0)+jk)
else
stib(leg(0))=jk
end if
if(cflag(confi%pq).eq.0)then
call qaocb(1)
Q_ERRT
j3=stcbs(1)
if(icom.eq.dekc%in)then
stcb(j3:j3)=achar(kpqs(2))
else
stcb(j3:j3)=achar(kpqs(3))
end if
leg(0)=leg(0)+1
stib(leg(0))=j3
call qdkar(i1,ii)
Q_ERRT
call qaocb(ii+1)
Q_ERRT
stcb(j3+1:stcbs(1))=zstr(1:ii)//achar(anull)
leg(0)=leg(0)+1
stib(leg(0))=stcbs(1)-1
leg(0)=leg(0)+1
stib(leg(0))=ii+1
else
j4=j2+6
if(stjb(j4-3).eq.alpar)then
if(cflag(confi%hidpq).ne.0)then
go to 80
end if
cflag(confi%hidpq)=nleg
end if
leg(0)=leg(0)+1
stib(leg(0))=stjb(j4)
leg(0)=leg(0)+1
stib(leg(0))=stjb(j4+1)
leg(0)=leg(0)+1
stib(leg(0))=stjb(j4+1)-(stjb(j4)-1)
end if
end do
else if(nphia.ne.0)then
go to 80
end if
if(icom.eq.dekc%out)then
stib(leg(0)+1:leg(0)+kk)=eoa
leg(0)=leg(0)+kk
ii=nleg+2
call qtrm(kk,ii,leg(0))
Q_ERRT
momel(0)=leg(0)-(ii-1)
momeq(0)=momel(0)-ii
momep(0)=momeq(0)-ii
leg(0)=momep(0)-ii
stib(leg(0))=eoa
stib(momep(0))=nap
stib(momeq(0))=nap
stib(momel(0))=-1
if(nleg.ne.inco+outg)then
qerrmsg(1:srec)='qinputs_8'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(nleg.eq.0)then
qerrt(0)=qerrty%inp
call qcfmsg(21,0,0)
Q_ERRT
end if
end if
go to 143
107 continue
if(stapi(2).ne.1)then
if(stapi(2).ne.2)then
go to 80
end if
end if
j1=pp1+7
loopx(1)=qstoz(stcb,stjb(j1),stjb(j1+1),inty%s)
Q_ERRT
loopx(2)=loopx(1)
if(stapi(2).eq.2)then
j1=j1+3
ij=0
call qmstr0(stcb,stjb(j1),stjb(j1+1),popt4(0),wopt4(0),aopt4(0),ij)
Q_ERRT
if(ij.le.0)then
go to 80
end if
j1=j1+3
loopx(2)=qstoz(stcb,stjb(j1),stjb(j1+1),inty%s)
Q_ERRT
end if
loopx(3)=min(loopx(1),loopx(2))
loopx(4)=max(loopx(1),loopx(2))
if(loopx(3).lt.0)then
qerrt(0)=qerrty%inp
call qcfmsg(26,0,0)
Q_ERRT
else if((loopx(4).gt.maxrho).or.&
(loopx(4)+nleg.gt.max(maxleg,maxrho)))then
qerrt(0)=qerrty%inp
call qcfmsg(27,0,0)
Q_ERRT
end if
if(nleg+loopx(3).lt.2)then
qerrt(0)=qerrty%inp
call qcfmsg(24,0,0)
Q_ERRT
end if
if((nleg.eq.2).and.&
(loopx(3).eq.0))then
qerrt(0)=qerrty%inp
call qcfmsg(23,0,0)
Q_ERRT
end if
if(loopx(4).eq.0)then
do i1=1,maxli
zcho(i1)=0
end do
end if
do i1=0,loopx(3)-1
zcho(i1)=0
end do
go to 143
108 continue
if(stapi(2).ne.1)then
go to 80
end if
j1=pp1+7
stib(momep(0))=stjb(j1)
stib(momeq(0))=stjb(j1+1)
stib(momel(0))=stjb(j1+1)-(stjb(j1)-1)
cflag(confi%loopk)=1
go to 143
109 continue
ii=0
j1=pp1+1
do i1=1,stapi(2)
j1=j1+6
ij=0
call qmstr0(stcb,stjb(j1),stjb(j1+1),popt1(0),wopt1(0),aopt1(0),ij)
Q_ERRT
if(ij.le.0)then
go to 80
end if
ik=stib(xopt1(0)+ij)
ij=stib(copt1(0)+ij)
if(dflag(ij).ne.0)then
ii=ii+1
if(dflag(ij)*ik.lt.0)then
jflag(jflaty%noga)=1
end if
end if
dflag(ij)=ik
end do
if(ii.gt.0)then
qerrt(0)=qerrty%ale
call qcfmsg(32,0,0)
Q_ERRT
end if
if(dflag(dflaty%topo).ne.0)then
dflag(dflaty%newa)=1
else if(dflag(dflaty%newe).ne.0)then
dflag(dflaty%newa)=1
else if(dflag(dflaty%newt).ne.0)then
dflag(dflaty%newa)=1
else if(dflag(dflaty%newp).ne.0)then
dflag(dflaty%newa)=1
else if(dflag(dflaty%newc).ne.0)then
dflag(dflaty%newa)=1
end if
if(qxmod.ne.qmod%fcon)then
if(cflag(confi%dspl).eq.dsplmod%vrbs)then
if(abs(dflag(dflaty%topo))+abs(dflag(dflaty%simp)).ne.0)then
if(qobsol(qobs%topol)+qobsol(qobs%simple).eq.0)then
qerrt(0)=qerrty%ale
call qiomsg(23,dbl,nlin,ifile)
Q_ERRT
qobsol(qobs%simple)=1
qobsol(qobs%topol)=1
end if
end if
end if
end if
go to 143
110 continue
if(stapi(2).eq.0)then
go to 80
else if(modulo(stapi(2),2).ne.0)then
go to 80
end if
cflag(confi%part)=1
vdpi(0)=stibs(1)+1
call qaoib(nrho+2)
Q_ERRT
stib(vdpi(0):stibs(1)-1)=-1
stib(stibs(1))=eoa
vdpj(0)=stibs(1)+1
call qaoib(nrho+2)
Q_ERRT
stib(vdpj(0):stibs(1)-1)=0
stib(stibs(1))=eoa
j1=pp1+4
ier=0
do i1=2,stapi(2),2
j1=j1+3
if(stjb(j1+1)-stjb(j1).gt.zbo%wiref)then
go to 80
end if
j2=qstoz(stcb,stjb(j1),stjb(j1+1),inty%s)
Q_ERRT
if(j2.lt.mrho)then
ier=1
else if(j2.gt.nrho)then
ier=1
else if(stib(nivd(0)+j2).eq.0)then
ier=1
else if(stib(vdpi(0)+j2).ge.0)then
ier=1
end if
if(ier.ne.0)then
exit
end if
j1=j1+6
if(stjb(j1-1).eq.strty%z)then
j4=0
j5=0
else
j1=j1+3
if(stjb(j1-1).eq.strty%z)then
j4=0
else if(stjb(j1-1).eq.strty%ns)then
j3=stjb(j1+1)
j3=iachar(stcb(j3:j3))
if(j3.eq.aplus)then
j4=1
else if(j3.eq.aminus)then
j4=-1
else
ier=1
exit
end if
else
ier=1
exit
end if
j5=3
end if
stib(vdpj(0)+j2)=j4
j4=abs(j4)
j3=qstoz(stcb,stjb(j1),stjb(j1+1)-j4,inty%s)
Q_ERRT
if(j3.lt.0)then
ier=1
exit
end if
j1=j1+j5
stib(vdpi(0)+j2)=j3
end do
if(ier.ne.0)then
qerrt(0)=qerrty%inp
call qcfmsg(33,0,0)
Q_ERRT
end if
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
go to 143
111 continue
if(stapi(2).ne.1)then
go to 80
end if
j1=pp1+7
j2=stjb(j1+1)
kk=qsigz(stcb,stjb(j1),j2)
Q_ERRT
if(kk.lt.0)then
go to 80
else if(kk.eq.0)then
go to 143
end if
cflag(confi%dioff)=1
j3=qilsd(stcb,stjb(j1),j2)
Q_ERRT
qcol(dcoty%offix)=j2-(j3-1)
qcol(dcoty%off)=qcol(dcoty%offix)
stcb(qcop(dcoty%offix)+1:qcop(dcoty%offix)+qcol(dcoty%offix))=stcb(j3:j2)
stcb(qcop(dcoty%off)+1:qcop(dcoty%off)+qcol(dcoty%off))=stcb(j3:j2)
go to 143
112 continue
if(qxmod.eq.qmod%api)then
go to 80
else if(stapi(2).ne.1)then
go to 80
end if
cflag(confi%qlist)=0
j1=pp1+7
j2=stjb(j1+1)
kk=qsigz(stcb,stjb(j1),j2)
Q_ERRT
if(kk.ne.1)then
go to 80
end if
j3=qilsd(stcb,stjb(j1),j2)
Q_ERRT
qcol(dcoty%maxc)=j2-(j3-1)
stcb(qcop(dcoty%maxc)+1:qcop(dcoty%maxc)+qcol(dcoty%maxc))=stcb(j3:j2)
cflag(confi%maxc)=1
go to 143
113 continue
if(stapi(2).ne.1)then
go to 80
end if
j1=pp1+7
momzp(0)=stjb(j1)
momzq(0)=stjb(j1+1)
momzl(0)=stjb(j1+1)-(stjb(j1)-1)
go to 143
130 continue
if(stapi(2).le.0)then
go to 80
end if
ntf=ntf+1
go to 143
143 continue
if((icom.eq.dekc%tru).or.&
(icom.eq.dekc%fal))then
j1=stjbs
nmp=nmp+1
ii=3
call qaojb(ii)
Q_ERRT
do i1=1,2
j1=j1+1
stjb(j1)=stapi(i1)
end do
j1=j1+1
stjb(j1)=ncom
else
call qaojb(-1)
Q_ERRT
end if
if(icom.eq.dekc%model)then
call qifi
Q_ERRT
ii=stjbs
do i1=1,nfiles
if(filp(i1).ne.nap)then
if(filt(i1).eq.qfty%styp)then
call qstyle
Q_ERRT
exit
end if
end if
end do
if(stjbs.ne.ii)then
qerrmsg(1:srec)='qinputs_9'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
call qmodel
Q_ERRT
if(stjbs.ne.ii)then
qerrmsg(1:srec)='qinputs_10'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
go to 03
301 continue
if(ntf.gt.0)then
ii=ntf+1
tftyp(0)=stibs(1)
jj=9*ii
call qaoib(jj)
Q_ERRT
tfnarg(0)=tftyp(0)+ii
tfa(0)=tfnarg(0)+ii
tfb(0)=tfa(0)+ii
tfc(0)=tfb(0)+ii
tf2(0)=tfc(0)+ii
tfo(0)=tf2(0)+ii
tfills(0)=tfo(0)+ii
tfiuls(0)=tfills(0)+ii
stib(tfills(0))=eoa
stib(tfiuls(0))=eoa
stib(tfnarg(0))=eoa
stib(tfa(0))=eoa
stib(tfb(0))=eoa
stib(tfc(0))=eoa
stib(tf2(0))=eoa
stib(tfo(0))=eoa
stib(stibs(1))=eoa
end if
ntf1=0
pp0=nap
nmp0=1
501 continue
do i1=nmp0,nmp
if(pp0.eq.nap)then
pp0=stjr0+1
else
pp0=stjb(pp0-2)+1
end if
pp1=pp0+1
pp2=pp1+3*(stjb(pp0)-1)
pp0=stjb(pp0-2)+1
icom=stjb(pp0)
nmp0=i1+1
j1=stjb(pp0+2)
if((icom.eq.dekc%tru).or.&
(icom.eq.dekc%fal))then
go to 611
else
go to 80
end if
end do
go to 701
611 continue
jj=stjb(pp1-1)
if(jj.lt.7)then
go to 80
end if
j1=stjb(pp1+7)
j2=stjb(pp1+8)
ij=0
call qmstr0(stcb,j1,j2,popt2(0),wopt2(0),aopt2(0),ij)
Q_ERRT
if(ij.eq.0)then
go to 80
end if
atyp=stib(copt2(0)+ij)
ktyp=stib(xopt2(0)+ij)
if(atyp.le.0)then
go to 80
else if(atyp.eq.opety%vsum)then
dflag(dflaty%vsum)=1
else if(atyp.eq.opety%psum)then
dflag(dflaty%psum)=1
else if(atyp.eq.opety%elink)then
dflag(dflaty%elink)=1
else if(atyp.eq.opety%plink)then
dflag(dflaty%plink)=1
end if
if(icom.eq.dekc%tru)then
tfv=1
else if(icom.eq.dekc%fal)then
tfv=-1
else
go to 80
end if
styp=atyp*tfv
j1=stjb(pp1-1)
j3=-1
if(ktyp.ne.opekty%link)then
j3=j1-8
j4=2
else if(atyp.eq.opety%elink)then
j3=j1-10
j4=3
else if(atyp.eq.opety%plink)then
j3=j1-4
j4=0
end if
if(j3.eq.0)then
j3=1
else if(j3.lt.0)then
go to 80
end if
j3=(j3-1)/2
if(ktyp.eq.opekty%link)then
if(j3.eq.0)then
go to 80
end if
end if
if(j4.gt.1)then
j1=qstoz(stcb,stjb(pp2-11),stjb(pp2-10),inty%s)
Q_ERRT
j2=qstoz(stcb,stjb(pp2-5),stjb(pp2-4),inty%s)
Q_ERRT
if(j1.gt.j2)then
go to 80
end if
if(ktyp.eq.opekty%bnb)then
if(j1.lt.0)then
go to 80
end if
if(atyp.ne.opety%iprop)then
jflag(jflaty%intlp)=1
end if
else if(atyp.eq.opety%elink)then
if(j1.le.0)then
go to 80
end if
end if
else
j1=0
j2=0
end if
if(j3.eq.0)then
go to 673
end if
ntf1=ntf1+1
stib(tftyp(0)+ntf1)=styp
stib(tfnarg(0)+ntf1)=j3
stib(tfa(0)+ntf1)=j1
stib(tfb(0)+ntf1)=j2
stib(tfc(0)+ntf1)=0
stib(tfo(0)+ntf1)=stibs(1)
call qaoib(j3+1)
Q_ERRT
if(dflag(dflaty%vsum).ne.0)then
stib(tfills(0)+ntf1)=stibs(1)
call qaoib(maxn+1)
Q_ERRT
stib(tfiuls(0)+ntf1)=stibs(1)
call qaoib(maxn+1)
Q_ERRT
end if
stib(stibs(1))=eoa
if(ktyp.ne.opekty%bnb)then
go to 637
end if
j4=stib(tfo(0)+ntf1)
ii=pp1+7
do i1=1,stib(tfnarg(0)+ntf1)
ii=ii+6
jk=0
call qmstr0(stcb,stjb(ii),stjb(ii+1),namep(0),namel(0),nap,jk)
Q_ERRT
if(jk.eq.0)then
qerrt(0)=qerrty%inp
call qcfmsg(36,dbl,nlin)
Q_ERRT
end if
stib(j4+i1)=jk
end do
call qhsort(j4+1,j4+stib(tfnarg(0)+ntf1))
Q_ERRT
tfcl=stib(tfnarg(0)+ntf1)
tfch=1
tfcn=1
i3=1
do i1=2,stib(tfnarg(0)+ntf1)
i2=j4+i1
if((stib(i2).eq.stib(i2-1)).or.&
(stib(i2).eq.stib(link(0)+stib(i2-1))))then
i3=i3+1
if(i3.gt.tfch)then
tfch=i3
end if
else
if(i3.lt.tfcl)then
tfcl=i3
end if
tfcn=tfcn+1
i3=1
end if
end do
if(i3.lt.tfcl)then
tfcl=i3
end if
if(tfcn.ne.nprop)then
tfcl=0
end if
if(styp.gt.0)then
do i2=0,maxli
if((i2*tfch.lt.stib(tfa(0)+ntf1)).or.&
(i2*tfcl.gt.stib(tfb(0)+ntf1)))then
if(styp.eq.opety%iprop)then
zpro(i2)=0
else if(styp.eq.opety%bridge)then
zbri(i2)=0
else if(styp.eq.opety%sbridge)then
sbri(i2)=0
else if(styp.eq.opety%rbridge)then
rbri(i2)=0
else if(styp.eq.opety%chord)then
zcho(i2)=0
end if
end if
end do
else if(styp.lt.0)then
do i2=0,maxli
if(i2*tfch.le.stib(tfb(0)+ntf1))then
if(i2*tfcl.ge.stib(tfa(0)+ntf1))then
if(-styp.eq.opety%iprop)then
zpro(i2)=0
else if(-styp.eq.opety%bridge)then
zbri(i2)=0
else if(-styp.eq.opety%sbridge)then
sbri(i2)=0
else if(-styp.eq.opety%rbridge)then
rbri(i2)=0
else if(-styp.eq.opety%chord)then
zcho(i2)=0
end if
end if
end if
end do
end if
go to 501
673 continue
if(styp.gt.0)then
do i2=0,maxli
if((i2.lt.j1).or.&
(i2.gt.j2))then
if(styp.eq.opety%iprop)then
zpro(i2)=0
else if(styp.eq.opety%bridge)then
zbri(i2)=0
else if(styp.eq.opety%sbridge)then
sbri(i2)=0
else if(styp.eq.opety%rbridge)then
rbri(i2)=0
else if(styp.eq.opety%chord)then
zcho(i2)=0
end if
end if
end do
else
do i2=0,maxli
if(i2.ge.j1)then
if(i2.le.j2)then
if(-styp.eq.opety%iprop)then
zpro(i2)=0
else if(-styp.eq.opety%bridge)then
zbri(i2)=0
else if(-styp.eq.opety%sbridge)then
sbri(i2)=0
else if(-styp.eq.opety%rbridge)then
rbri(i2)=0
else if(-styp.eq.opety%chord)then
zcho(i2)=0
end if
end if
end if
end do
end if
go to 501
637 continue
if(atyp.eq.opety%vsum)then
if(stib(tfnarg(0)+ntf1).ne.1)then
go to 80
end if
j1=stjb(pp1+13)
j2=stjb(pp1+14)
kid=0
call qmstr0(stcb,j1,j2,vmkp(0),vmkl(0),nap,kid)
Q_ERRT
serrt=qerrty%ok
if(kid.gt.0)then
if(kid.gt.nvmk)then
serrt=qerrty%q
else if(stib(vmkt(0)+kid).ne.futyp%z)then
serrt=qerrty%inp
end if
else
serrt=qerrty%q
end if
if(kid.eq.0)then
qerrt(0)=qerrty%inp
call qcfmsg(36,dbl,nlin)
Q_ERRT
end if
stib(vmks(0)+kid)=1
stib(stib(tfo(0)+ntf1)+1)=kid
else if(atyp.eq.opety%psum)then
if(stib(tfnarg(0)+ntf1).ne.1)then
go to 80
end if
j1=stjb(pp1+13)
j2=stjb(pp1+14)
kid=0
call qmstr0(stcb,j1,j2,pmkp(0),pmkl(0),nap,kid)
Q_ERRT
if(kid.gt.0)then
if(kid.gt.npmk)then
kid=0
else if(stib(pmkt(0)+kid).ne.futyp%z)then
kid=0
else if(stib(pmkd(0)+kid).ne.1)then
kid=0
end if
else
kid=0
end if
if(kid.eq.0)then
qerrt(0)=qerrty%inp
call qcfmsg(36,dbl,nlin)
Q_ERRT
end if
stib(stib(tfo(0)+ntf1)+1)=kid
j1=stib(pmkvmi(0)+kid)
j2=stib(pmkvma(0)+kid)
do i2=0,maxli
if(styp.gt.0)then
if((i2*j1.gt.stib(tfb(0)+ntf1)).or.&
(i2*j2.lt.stib(tfa(0)+ntf1)))then
zpro(i2)=0
end if
else
if((i2*j1.ge.stib(tfa(0)+ntf1)).and.&
(i2*j2.le.stib(tfb(0)+ntf1)))then
zpro(i2)=0
end if
end if
end do
else if(ktyp.eq.opekty%link)then
if(nleg.lt.2)then
qerrt(0)=qerrty%inp
call qcfmsg(36,0,0)
Q_ERRT
end if
j3=stib(tfnarg(0)+ntf1)
if(j3.le.0)then
go to 80
else if(j3.gt.nleg)then
go to 80
end if
if(atyp.eq.opety%elink)then
if(j3.lt.stib(tfb(0)+ntf1))then
go to 80
end if
else if(atyp.eq.opety%plink)then
if(j3.eq.nleg)then
go to 80
end if
end if
if(nleg.gt.0)then
xli(1:nleg)=0
end if
do i1=1,j3
j1=pp1+7+6*i1
j2=qstoz(stcb,stjb(j1),stjb(j1+1),inty%s)
Q_ERRT
if(j2.ge.0)then
go to 80
else if(j2+2*nleg.lt.0)then
go to 80
end if
j1=(-j2)/2
if(j2+2*j1.eq.0)then
j1=j1+inco
if(j1.gt.nleg)then
go to 80
end if
else
j1=j1+1
if(j1.gt.inco)then
go to 80
end if
end if
if(xli(j1).ne.0)then
go to 80
end if
xli(j1)=1
j4=stib(tfo(0)+ntf1)
stib(j4+i1)=j1
end do
if(atyp.eq.opety%elink)then
j1=pp1+13+6*j3
ij=0
call qmstr0(stcb,stjb(j1),stjb(j1+1),popt3(0),wopt3(0),aopt3(0),ij)
Q_ERRT
if(ij.le.0)then
go to 80
end if
j1=stib(copt3(0)+ij)
stib(tfc(0)+ntf1)=j1
j2=0
if(j1.eq.elinty%excl)then
if(j3.eq.nleg)then
if(stib(tfa(0)+ntf1).eq.1)then
if(stib(tfb(0)+ntf1).eq.nleg)then
j2=styp
end if
end if
end if
else if(j1.eq.elinty%incl)then
if(stib(tfa(0)+ntf1).eq.1)then
if(stib(tfb(0)+ntf1).eq.j3)then
j2=styp
end if
end if
end if
if(j2.ne.0)then
if(j2.gt.0)then
qerrt(0)=qerrty%ale
call qcfmsg(38,0,0)
Q_ERRT
else
jflag(jflaty%noga)=1
qerrt(0)=qerrty%ale
call qcfmsg(37,0,0)
Q_ERRT
end if
end if
end if
else
qerrmsg(1:srec)='qinputs_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
go to 501
701 continue
call qsp(3,0,0)
Q_ERRT
if(skep(82).gt.0)then
if(comc(dekc%off).eq.0)then
qerrt(0)=qerrty%ale
call qcfmsg(34,0,0)
Q_ERRT
end if
end if
if(skep(86).gt.0)then
if(comc(dekc%loopk).eq.0)then
qerrt(0)=qerrty%inp
call qcfmsg(28,0,0)
Q_ERRT
end if
end if
if(skep(87).gt.0)then
if(comc(dekc%zerok).eq.0)then
qerrt(0)=qerrty%ale
call qcfmsg(29,0,0)
Q_ERRT
end if
end if
deltasub=2*max(inco,outg+1)
vmkmio(0)=nap
vmkmao(0)=nap
if(dflag(dflaty%vsum).ne.0)then
call qvsig
Q_ERRT
end if
i1=0
kk=0
705 continue
i1=i1+1
j1=stib(copt2(0)+i1)
if(j1.gt.0)then
ik=i1
if(j1.gt.kk)then
kk=j1
else if(j1.lt.kk)then
qerrmsg(1:srec)='qinputs_5'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
go to 705
end if
ii=ncopt2+1
jj=2*ii
call qaoib(jj)
Q_ERRT
tftb(0)=stibs(1)-ii
tfta(0)=tftb(0)-ii
stib(tftb(0))=eoa
stib(stibs(1))=eoa
jj=mcopt2+1
tftic(0)=stibs(1)
call qaoib(jj)
Q_ERRT
stib(stibs(1))=eoa
if(mcopt2.gt.0)then
stib(tftic(0)+1:tftic(0)+mcopt2)=nap
end if
do i1=1,ncopt2
j1=stib(copt2(0)+i1)
if(stib(tftic(0)+j1).eq.nap)then
stib(tftic(0)+j1)=i1
end if
end do
if(ncopt2.gt.0)then
stib(tfta(0)+1:tfta(0)+ncopt2)=0
stib(tftb(0)+1:tftb(0)+ncopt2)=-1
end if
ii=0
do i1=1,mcopt2
j1=stib(tftic(0)+i1)
if(j1.gt.0)then
do i2=1,ntf
if(abs(stib(tftyp(0)+i2)).eq.i1)then
ii=ii+1
if(stib(tfta(0)+j1).eq.0)then
stib(tfta(0)+j1)=ii
end if
stib(tftb(0)+j1)=ii
stib(tf2(0)+ii)=i2
end if
end do
end if
end do
serrt=qerrty%ok
if(cflag(confi%loopk).ne.0)then
j1=stcbs(1)+1
j3=stib(momel(0))
j2=j1+(j3-1)
call qdkar(loopx(4),j4)
Q_ERRT
ii=j3+j4
call qaocb(ii)
Q_ERRT
stcb(j1:j2)=stcb(stib(momep(0)):stib(momeq(0)))
do i1=1,loopx(4)
if(cflag(confi%pq).ne.0)then
call qdkar(i1,jk)
Q_ERRT
ik=j2+jk
stcb(j2+1:ik)=zstr(1:jk)
do i2=1,nleg
if(stib(momel(0))+jk.eq.stib(momel(0)+i2))then
if(stcb(j1:ik).eq.stcb(stib(momep(0)+i2):stib(momeq(0)+i2)))then
serrt=qerrty%inp
exit
end if
end if
end do
end if
if(comc(dekc%zerok).gt.0)then
if(stib(momel(0))+jk.eq.momzl(0))then
if(stcb(j1:ik).eq.stcb(momzp(0):momzq(0)))then
serrt=qerrty%inp
end if
end if
end if
if(serrt.ne.qerrty%ok)then
exit
end if
end do
call qaocb(-ii)
Q_ERRT
end if
if(comc(dekc%zerok).gt.0)then
if(cflag(confi%pq).ne.0)then
if(serrt.eq.qerrty%ok)then
do i1=1,nleg
if(momzl(0).eq.stib(momel(0)+i1))then
if(stcb(momzp(0):momzq(0)).eq.stcb(stib(momep(0)+i1):stib(momeq(0)+i1)))then
serrt=qerrty%inp
exit
end if
end if
end do
end if
end if
end if
if(cflag(confi%pq).ne.0)then
do i1=1,nleg
if(serrt.eq.qerrty%ok)then
do i2=i1+1,nleg
if(stib(momel(0)+i1).eq.stib(momel(0)+i2))then
if(stcb(stib(momep(0)+i1):stib(momeq(0)+i1)).eq.stcb(stib(momep(0)+i2):stib(momeq(0)+i2)))then
serrt=qerrty%inp
exit
end if
end if
end do
else
exit
end if
end do
end if
if(serrt.ne.qerrty%ok)then
serrt=qerrty%ok
if(jflag(jflaty%smom).ne.0)then
qerrt(0)=qerrty%inp
else
qerrt(0)=qerrty%ale
end if
call qcfmsg(31,0,0)
Q_ERRT
end if
if(cflag(confi%qlist).gt.0)then
if(jflag(jflaty%smom).ne.0)then
if(cflag(confi%pq).eq.0)then
if(nleg.gt.0)then
qerrt(0)=qerrty%inp
call qcfmsg(19,0,0)
Q_ERRT
end if
end if
if(cflag(confi%loopk).eq.0)then
if(loopx(4).gt.0)then
qerrt(0)=qerrty%inp
call qcfmsg(28,0,0)
Q_ERRT
end if
end if
end if
end if
if(nleg.gt.0)then
if(nleg.gt.1)then
ii=abs(stib(blok(0)+stib(leg(0)+1)))
do i1=2,nleg
if(abs(stib(blok(0)+stib(leg(0)+i1))).ne.ii)then
qerrt(0)=qerrty%ale
call qcfmsg(17,0,0)
Q_ERRT
jflag(jflaty%noga)=1
exit
end if
end do
end if
ii=1
do i1=1,nleg
if(stib(antiq(0)+stib(leg(0)+i1)).ne.0)then
ii=-ii
end if
end do
if(ii.lt.0)then
qerrt(0)=qerrty%ale
call qcfmsg(14,0,0)
Q_ERRT
jflag(jflaty%noga)=1
end if
do i1=1,nleg
j1=stib(link(0)+stib(leg(0)+i1))
if(stib(blok(0)+j1).lt.0)then
qerrt(0)=qerrty%ale
call qcfmsg(16,0,0)
Q_ERRT
jflag(jflaty%noga)=1
exit
end if
j2=stib(tpc(0)+j1)
if((j2.eq.phity%int).or.&
(j2.eq.phity%ntint))then
qerrt(0)=qerrty%inp
call qcfmsg(18,0,0)
Q_ERRT
end if
end do
end if
do i1=1,nphi
j1=tpc(0)+i1
if(stib(j1).eq.phity%int)then
stib(j1)=phity%dflt
else if(stib(j1).eq.phity%ntint)then
stib(j1)=phity%notdp
end if
end do
do i1=1,2*nmp
call qaojb(-1)
Q_ERRT
end do
if((nstjb.ne.0).or.&
(stjbs.ne.stj0))then
qerrmsg(1:srec)='qinputs_7'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(cflag(confi%qlist).gt.0)then
call qiki
Q_ERRT
end if
call qrflag0
Q_ERRT
vsfi(0)=nap
psfi(0)=nap
nivdx(0)=nap
if((dflag(dflaty%vsum).ne.0).or.&
(dflag(dflaty%psum).ne.0))then
call qvsf
Q_ERRT
end if
efm(0)=stibs(1)
ii=nleg+1
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
efinvdc(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
do i1=1,ii-1
stib(efm(0)+i1)=0
stib(efinvdc(0)+i1)=nap
end do
d01: do i1=1,nleg
jj=stib(link(0)+stib(leg(0)+i1))
do i2=1,i1-1
if(stib(link(0)+stib(leg(0)+i2)).eq.jj)then
stib(efm(0)+i1)=-stib(efm(0)+i2)
stib(efinvdc(0)+i1)=stib(efinvdc(0)+i2)
cycle d01
end if
end do
do i2=1,nleg
if(stib(link(0)+stib(leg(0)+i2)).eq.jj)then
stib(efm(0)+i1)=stib(efm(0)+i1)+1
end if
end do
j1=stibs(1)
stib(efinvdc(0)+i1)=j1
call qaoib(nrho+1)
Q_ERRT
stib(j1+1:j1+nrho)=0
stib(stibs(1))=eoa
do i2=mrho,nrho
if(stib(nivd(0)+i2).gt.0)then
j1=0
do i3=1,nvert
if(stib(vval(0)+i3).eq.i2)then
j2=0
j3=stib(vparto(0)+i3)
do i4=1,i2
if(stib(j3+i4).eq.jj)then
j2=j2+1
end if
end do
if(j2.gt.j1)then
j1=j2
end if
end if
end do
stib(stib(efinvdc(0)+i1)+i2)=j1
end if
end do
end do d01
call qindg
Q_ERRT
go to 99
80 continue
qerrt(0)=max(qerrty%inp,serrt)
call qcfmsg0(1,dbl,nlin)
Q_ERRT
99 continue
return
end subroutine qinputs
subroutine qindg
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::i1
if(qxmod.eq.qmod%auto)then
if(cflag(confi%qlist).gt.0)then
cflag(confi%nontlf)=0
call qpropos
Q_ERRT
end if
end if
do i1=1,nfiles
if((filt(i1).eq.qfty%ctyp).or.&
(filt(i1).eq.qfty%styp).or.&
(filt(i1).eq.qfty%mtyp))then
if(filu(i1).ne.non_unit)then
call qclose(i1)
Q_ERRT
end if
end if
end do
99 continue
return
end subroutine qindg
subroutine qsetfname(fty0,i1,i2,ll)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::fty0,i1,i2
integer(kind=c_int_least32_t),intent(inout)::ll
integer(kind=c_int_least32_t), external::qstdpa
integer(kind=c_int_least32_t)::j1,j2,j3
if(cflag(confi%noblank).gt.0)then
if(fty0.ne.qfty%ptyp)then
if((fty0.ne.qfty%ctyp).or.&
(qxmod.eq.qmod%api))then
call qnows(i1,i2,ll)
Q_ERRT
end if
end if
end if
ll=i2-1-i1
if(ll.gt.0)then
if((iachar(stcb(i1:i1)).eq.asq).and.(iachar(stcb(i2:i2)).eq.asq))then
j1=i1+1
j2=i2-1
else
qerrt(0)=qerrty%inp
call qiomsg(13,0,0,nfiles)
Q_ERRT
end if
if(iachar(stcb(j2:j2)).eq.p_sep)then
qerrt(0)=qerrty%inp
call qiomsg(13,0,0,nfiles)
Q_ERRT
end if
nfiles=nfiles+1
filp(nfiles)=j1
filq(nfiles)=j2
filt(nfiles)=fty0
j3=qstdpa(stcb,j1,j2)
Q_ERRT
if(j3.eq.0)then
qerrt(0)=qerrty%inp
call qiomsg(13,0,0,nfiles)
Q_ERRT
end if
if(fty0.eq.qfty%styp)then
nsfiles=nsfiles+1
end if
if((fty0.eq.qfty%otyp).or.&
(fty0.eq.qfty%wtyp))then
fild(nfiles)=qfdty%dok
else
fild(nfiles)=qfdty%dno
end if
end if
99 continue
return
end subroutine qsetfname
subroutine qsetudir(p0,q0,stjr,dtyp)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::p0,q0,stjr,dtyp
integer(kind=c_int_least32_t), external::qstdpa
integer(kind=c_int_least32_t)::i1,i2,ii,j1,j2,ll
ll=-1
if(stapi(2).eq.0)then
ll=0
else if(stapi(2).eq.1)then
j1=stjr+9
if(cflag(confi%noblank).gt.0)then
call qnows(stjb(j1),stjb(j1+1),j1)
Q_ERRT
end if
ll=stjb(j1+1)-1-stjb(j1)
end if
if(ll.gt.0)then
j2=stjb(j1+1)-1
j2=iachar(stcb(j2:j2))
if(cflag(confi%psep).eq.0)then
if((acf(j2).gt.0).or.&
(j2.eq.aspc))then
qerrt(0)=qerrty%q
call qcfmsg(7,0,0)
Q_ERRT
end if
cflag(confi%psep)=-1
p_sep=j2
else if(cflag(confi%psep).lt.0)then
if(j2.ne.p_sep)then
qerrt(0)=qerrty%inp
call qcfmsg(7,0,0)
Q_ERRT
end if
end if
serrt=qerrty%ok
if(udirpq(p0).eq.nap)then
udirpq(p0)=stjb(j1)+1
udirpq(q0)=stjb(j1+1)-1
ii=qstdpa(stcb,udirpq(p0),udirpq(q0))
Q_ERRT
if(ii.eq.0)then
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(13,0,0,mfiles0+dtyp)
Q_ERRT
end if
if(cflag(confi%psep).ne.0)then
if(iachar(stcb(udirpq(q0):udirpq(q0))).eq.p_sep)then
udirpq(q0)=udirpq(q0)-1
end if
end if
do i1=2,udir%ubo,2
if(udirpq(i1).ne.nap)then
do i2=i1+2,udir%ubo,2
if(udirpq(i2).ne.nap)then
if(udirpq(i1)-udirpq(i1-1).eq.udirpq(i2)-udirpq(i2-1))then
if(stcb(udirpq(i1-1):udirpq(i1)).eq.stcb(udirpq(i2-1):udirpq(i2)))then
serrt=qerrty%inp
exit
end if
end if
end if
end do
end if
end do
else
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qcfmsg(6,0,0)
Q_ERRT
end if
else
qerrt(0)=qerrty%inp
call qiomsg(13,0,0,mfiles0+dtyp)
Q_ERRT
end if
99 continue
return
end subroutine qsetudir
subroutine qiki
use,non_intrinsic::qcbuffer
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::i1,i2,j1,j2,jj,kk
do i1=1,nudk
j1=stib(udkp(0)+i1)
j2=j1-1+stib(udkl(0)+i1)
kk=0
jj=0
call qmstr0(stcb,j1,j2,gmkp(0),gmkl(0),nap,jj)
Q_ERRT
if(jj.gt.0)then
kk=1
end if
if(kk.eq.0)then
jj=0
call qmstr0(stcb,j1,j2,pmkp(0),pmkl(0),nap,jj)
Q_ERRT
if(jj.gt.0)then
kk=2
end if
end if
if(kk.eq.0)then
jj=0
call qmstr0(stcb,j1,j2,vmkp(0),vmkl(0),nap,jj)
Q_ERRT
if(jj.gt.0)then
kk=3
end if
end if
if(kk.eq.0)then
call qstymsg(2,0,0,0,j1,j2)
Q_ERRT
end if
stib(udkt(0)+i1)=kk
stib(udki(0)+i1)=jj
end do
j1=udkp(1)
do i1=1,nudk
j1=stib(j1)
if(stib(udkt(0)+i1).eq.1)then
do i2=3,7
if(stib(j1+i2).gt.1)then
call qstymsg(3,0,0,0,0,0)
Q_ERRT
end if
end do
else if(stib(udkt(0)+i1).eq.2)then
if(stib(j1+3).ne.0)then
call qstymsg(4,0,0,0,0,0)
Q_ERRT
end if
if(stib(pmkd(0)+stib(udki(0)+i1)).eq.3)then
if(stib(j1+6).ne.0)then
call qstymsg(5,0,0,0,0,0)
Q_ERRT
end if
else
if(stib(j1+6).ne.0)then
call qstymsg(5,0,0,0,0,0)
Q_ERRT
end if
do i2=4,7
if(stib(j1+i2).gt.1)then
call qstymsg(7,0,0,0,0,0)
Q_ERRT
end if
end do
end if
else if(stib(udkt(0)+i1).eq.3)then
if(stib(j1+3).ne.0)then
call qstymsg(4,0,0,0,0,0)
Q_ERRT
end if
do i2=4,7
if((i2.ne.5).and.&
(stib(j1+i2).gt.1))then
call qstymsg(8,0,0,0,0,0)
Q_ERRT
end if
end do
end if
end do
99 continue
return
end subroutine qiki
subroutine qrsfki
use,non_intrinsic::qimodel
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::ii,i1,j1
ii=nudk+1
udkp(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
udkl(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
udkt(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
udki(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
if(nudk.gt.0)then
stib(udkt(0)+1:udkt(0)+nudk)=0
stib(udki(0)+1:udki(0)+nudk)=0
j1=udkp(1)
do i1=1,nudk
j1=stib(j1)
stib(udkp(0)+i1)=stib(j1+1)
stib(udkl(0)+i1)=stib(j1+2)
end do
end if
99 continue
return
end subroutine qrsfki
subroutine qvsig
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstoz
integer(kind=c_int_least32_t)::ii,ij,jj,i1,i2,j1,j2,p1,p2,p3
ii=nvmk+1
vmkzp(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
vmkmio(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
vmkmao(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
do i1=1,nvmk
if(stib(vmks(0)+i1).eq.0)then
stib(vmkzp(0)+i1)=nap
stib(vmkmio(0)+i1)=nap
stib(vmkmao(0)+i1)=nap
else
p3=stibs(1)
stib(vmkzp(0)+i1)=p3
ii=nvert
call qaoib(ii)
Q_ERRT
ii=nrho
p1=stibs(1)
stib(vmkmio(0)+i1)=p1
call qaoib(ii)
Q_ERRT
p2=stibs(1)
stib(vmkmao(0)+i1)=p2
call qaoib(ii)
Q_ERRT
call qvaoib(ii)
Q_ERRT
stib(stibs(1)+1:stibs(1)+ii)=0
ii=stib(vmkvpp(0)+i1)
jj=stib(vmkvlp(0)+i1)
do i2=1,nvert
j1=stib(ii+i2)
j2=(j1-1)+stib(jj+i2)
ij=qstoz(stcb,j1,j2,inty%s)
Q_ERRT
stib(p3+i2)=ij
j1=stib(vval(0)+i2)
j2=stibs(1)+j1
if(stib(j2).ne.0)then
if(ij.gt.stib(p2+j1))then
stib(p2+j1)=ij
else if(ij.lt.stib(p1+j1))then
stib(p1+j1)=ij
end if
else
stib(j2)=1
stib(p1+j1)=ij
stib(p2+j1)=ij
end if
end do
end if
end do
if(stib(stibs(1)).ne.eoa)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
end if
99 continue
return
end subroutine qvsig
subroutine qg10
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::ii,i1,i2,i3,i4,i5,jj,j1,j2,j3,kk
integer(kind=c_int_least32_t)::atyp,aux,a1,a2,b1,b2,styp
integer(kind=c_int_least32_t)::vaux(1:maxli),xli(1:maxleg),xlj(1:maxn)
if(qcntrx.eq.qcntr%e)then
qcntrx=qcntr%d
end if
outd(qcntr%e)=0
qco(qcntr%e)=0
if(qcntrx.lt.qcntr%t)then
qcntrx=qcntr%d
go to 29
end if
27 continue
call qg21
Q_ERRT
if(qco(qcntr%t).eq.0)then
go to 99
end if
do i1=1,n
vaux(i1)=xn(i1)
end do
do i1=1,rho(-1)
vlis(i1)=i1
invlis(i1)=i1
end do
do i1=rhop1,n
invlis(i1)=0
end do
aux=rho(-1)
jj=rhop1
10 continue
if(aux.lt.n)then
20 continue
if(invlis(jj).ne.0)then
jj=jj+1
go to 20
end if
ii=jj
do i1=ii+1,n
if(invlis(i1).eq.0)then
if(vaux(i1).gt.vaux(ii))then
ii=i1
end if
end if
end do
if(vaux(ii).eq.0)then
qerrmsg(1:srec)='qg10_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
aux=aux+1
vlis(aux)=ii
invlis(ii)=aux
rdeg(ii)=vaux(ii)
sdeg(ii)=rdeg(ii)+gam(ii,ii)
do i1=rhop1,n
vaux(i1)=vaux(i1)+gam(i1,ii)
end do
go to 10
end if
if(n.gt.0)then
vaux(1:n)=0
end if
do i1=1,n
ii=vlis(i1)
kk=0
j1=1
30 continue
if(kk.lt.vdeg(ii))then
jj=vlis(j1)
aux=1
do i3=1,gam(ii,jj)
kk=kk+1
vmap(ii,kk)=jj
vaux(jj)=vaux(jj)+1
if(ii.ne.jj)then
lmap(ii,kk)=vaux(jj)
else
lmap(ii,kk)=vaux(jj)+aux
aux=-aux
end if
end do
j1=j1+1
go to 30
end if
if(kk.ne.vdeg(ii))then
qerrmsg(1:srec)='qg10_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
do i1=rhop1,n
do i2=1,vdeg(i1)-1
if(invlis(vmap(i1,i2)).gt.invlis(vmap(i1,i2+1)))then
qerrmsg(1:srec)='qg10_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
end do
do i1=1,n
do i2=1,vdeg(i1)
j1=vmap(i1,i2)
j2=lmap(i1,i2)
if(vmap(j1,j2).ne.i1)then
qerrmsg(1:srec)='qg10_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(lmap(j1,j2).ne.i2)then
qerrmsg(1:srec)='qg10_5'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
end do
if((cflag(confi%qlist).gt.0).or.&
(jflag(jflaty%intlp).gt.0))then
do i1=rhop1,n
do i2=1,vdeg(i1)
j3=vmap(i1,i2)
if(j3.gt.rho(-1))then
j1=min(i1,j3)
j2=max(i1,j3)
ii=ege(j1,j2)
jj=gam(i1,j3)-1
if(jj.eq.0)then
amap(i1,i2)=ii
else if(i1.eq.j3)then
amap(i1,i2)=ii+((i2-1-rdeg(i1))/2)
else
kk=0
do i3=i2-1,1,-1
if(vmap(i1,i3).eq.j3)then
kk=kk+1
else
exit
end if
end do
amap(i1,i2)=ii+kk
end if
end if
end do
end do
end if
if(dflag(dflaty%cyc).ne.0)then
call qcyc(1,j1)
Q_ERRT
if(j1.ne.dflag(dflaty%cyc))then
go to 27
end if
end if
do i1=1,rho(-1)
ps1(i1)=i1
end do
go to 70
29 continue
do i1=rho(-1)-1,1,-1
if(ps1(i1).lt.ps1(i1+1))then
j1=i1
go to 38
end if
end do
go to 27
38 continue
do i1=j1+2,rho(-1)
if(ps1(i1).lt.ps1(j1))then
j2=i1-1
go to 61
end if
end do
j2=rho(-1)
61 continue
ii=ps1(j1)
ps1(j1)=ps1(j2)
ps1(j2)=ii
j1=j1+1
j2=rho(-1)
33 continue
if(j1.lt.j2)then
ii=ps1(j1)
ps1(j1)=ps1(j2)
ps1(j2)=ii
j1=j1+1
j2=j2-1
go to 33
end if
70 continue
do i1=1,ns1
if(ps1(p1r(i1)).lt.ps1(p1l(i1)))then
do i2=p1r(i1)+1,rho(-1)-1
do i3=i2+1,rho(-1)
if(ps1(i2).lt.ps1(i3))then
ii=ps1(i2)
ps1(i2)=ps1(i3)
ps1(i3)=ii
end if
end do
end do
go to 29
end if
end do
do i1=1,rho(-1)
invps1(ps1(i1))=i1
end do
if(dflag(dflaty%idx).ne.0)then
do i2=1,rho(-1)
ii=stib(leg(0)+i2)
do i3=i2+1,rho(-1)
if(ii.eq.stib(leg(0)+i3))then
if(invps1(i2).gt.invps1(i3))then
go to 29
end if
end if
end do
end do
end if
if(nrho.gt.mrho)then
if(mflag(mflaty%one).eq.0)then
do i1=1,rho(-1)
j1=stib(link(0)+stib(leg(0)+ps1(i1)))
j2=stib(dpntro(0)+vdeg(vmap(i1,1)))
if(stib(stib(j2+j1)+1).ne.j1)then
go to 29
end if
end do
end if
end if
if(dflag(dflaty%elink).ne.0)then
ii=stib(tftic(0)+opety%elink)
do i1=stib(tfta(0)+ii),stib(tftb(0)+ii)
i3=stib(tf2(0)+i1)
styp=stib(tftyp(0)+i3)
j1=stib(tfnarg(0)+i3)
j2=stib(tfo(0)+i3)
do i2=rhop1,n
xlj(i2)=0
end do
ii=0
do i2=1,j1
j3=vmap(invps1(stib(j2+i2)),1)
if(xlj(j3).eq.0)then
xlj(j3)=1
ii=ii+1
end if
end do
if((ii.lt.stib(tfa(0)+i3)).or.&
(ii.gt.stib(tfb(0)+i3)))then
if(styp.gt.0)then
go to 29
else
go to 55
end if
end if
if(stib(tfc(0)+i3).eq.elinty%incl)then
if(styp.lt.0)then
go to 29
end if
else if(stib(tfc(0)+i3).eq.elinty%excl)then
if(rho(-1).gt.0)then
xli(1:rho(-1))=0
end if
do i2=1,j1
xli(invps1(stib(j2+i2)))=1
end do
do i2=1,rho(-1)
if(xli(i2).eq.0)then
if(xlj(vmap(i2,1)).ne.0)then
if(styp.gt.0)then
go to 29
else
go to 55
end if
end if
end if
end do
if(styp.lt.0)then
go to 29
end if
end if
55 continue
end do
end if
if(dflag(dflaty%plink).ne.0)then
ii=stib(tftic(0)+opety%plink)
d02: do i2=stib(tfta(0)+ii),stib(tftb(0)+ii)
j3=stib(tf2(0)+i2)
styp=stib(tftyp(0)+j3)
j1=stib(tfnarg(0)+j3)
j2=stib(tfo(0)+j3)
if(rho(-1).gt.0)then
xli(1:rho(-1))=0
end if
do i3=1,j1
xli(invps1(stib(j2+i3)))=1
end do
do i3=rhop1,nli
if(flow(i3,0).eq.edgty%rb)then
kk=0
do i4=1,rho(-1)
if(flow(i3,i4).eq.0)then
if(xli(i4).ne.0)then
kk=kk+1
end if
else
if(xli(i4).eq.0)then
kk=kk+1
end if
end if
end do
if(kk.gt.0)then
kk=kk-rho(-1)
end if
if(kk.eq.0)then
if(styp.gt.0)then
cycle d02
else
go to 29
end if
end if
end if
end do
if(styp.gt.0)then
go to 29
end if
end do d02
end if
do i1=1,rho(-1)
amap(i1,1)=i1
amap(vmap(i1,1),lmap(i1,1))=i1
end do
if(dflag(dflaty%vsum).ne.0)then
do i1=1,ntf
styp=stib(tftyp(0)+i1)
atyp=abs(styp)
if(atyp.ne.opety%vsum)then
cycle
end if
j3=stib(stib(tfo(0)+i1)+1)
a1=stib(vmkmio(0)+j3)
b1=stib(vmkmao(0)+j3)
i3=stib(tfills(0)+i1)
i4=stib(tfiuls(0)+i1)
a2=-stib(tfa(0)+i1)
b2=-stib(tfb(0)+i1)
do i2=n,rhop1,-1
i5=vdeg(vlis(i2))
if(styp.gt.0)then
a2=a2+stib(b1+i5)
b2=b2+stib(a1+i5)
else
a2=a2+stib(a1+i5)
b2=b2+stib(b1+i5)
end if
stib(i3+i2)=a2
stib(i4+i2)=b2
end do
end do
end if
ex0(1:nli)=0
ey0(1:nli)=0
do i1=rhop1,n
do i2=1,vdeg(i1)
if(vmap(i1,i2).gt.nleg)then
if(vmap(i1,i2).lt.i1)then
cycle
else if((vmap(i1,i2).eq.i1).and.&
(modulo(i2-rdeg(i1),2).eq.0))then
cycle
end if
j1=amap(i1,i2)-nleg
if(j1.gt.0)then
ex0(j1)=i1
ey0(j1)=i2
end if
end if
end do
end do
if(jflag(jflaty%intlp).gt.0)then
if(cflag(confi%qlist).gt.0)then
call qflow
Q_ERRT
end if
end if
if(cflag(confi%qlist).gt.0)then
do i1=1,nli
vaux(i1)=-2
end do
do i1=1,n
do i2=1,vdeg(i1)
ii=amap(i1,i2)
if(ii.gt.0)then
if(ii.le.nli)then
vaux(ii)=vaux(ii)+1
end if
end if
end do
end do
do i1=1,nli
if(vaux(i1).ne.0)then
qerrmsg(1:srec)='qg10_7'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
end if
qco(qcntr%e)=1
99 continue
return
end subroutine qg10
subroutine qg21
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::bond,dsum,limax,limin,lin,loop,msum,n1,ntree
integer(kind=c_int_least32_t)::aux,col,ii,i1,i2,i3,i4,jj,j1,j2,j3,j4,kk
integer(kind=c_int_least32_t)::xc(1:maxdeg)
integer(kind=c_int_least32_t)::xl(1:maxn),xt(1:maxn)
integer(kind=c_int_least32_t)::bound(1:maxdeg),degr(1:maxdeg),xs(1:maxn)
integer(kind=c_int_least32_t)::xg(1:maxn,1:maxn),ds(1:maxn,1:maxn)
integer(kind=c_int_least32_t)::p1s(1:maxleg,1:maxleg)
integer(kind=c_int_least32_t)::aa(1:maxn),bb(1:maxn)
integer(kind=c_int_least32_t)::uset(0:maxn),xset(1:maxn),xp(1:maxn),a1(1:maxn)
integer(kind=c_int_least32_t)::str(1:maxn),dta(1:maxn),lps(1:maxn)
integer(kind=c_int_least32_t)::head(1:maxli),tail(1:maxli),intree(1:maxli)
integer(kind=c_int_least32_t)::emul(1:maxdeg,1:maxli),nemul(1:maxdeg)
serrt=qerrty%ok
if(nrho.lt.mrho)then
serrt=qerrty%q
else if(mrho.le.0)then
serrt=qerrty%q
else
do i1=-1,nrho
if((rho(i1).lt.0).or.&
(rho(i1).gt.maxn))then
serrt=qerrty%q
exit
end if
end do
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qg21_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
outd(qcntr%t)=0
qco(qcntr%t)=0
if(qcntrx.lt.qcntr%p)then
qcntrx=qcntr%d
go to 05
end if
27 continue
call qpg11
Q_ERRT
if(qco(qcntr%p).eq.0)then
go to 99
end if
n=0
do i1=1,rho(-1)
n=n+1
vdeg(n)=1
end do
jj=rho(-1)
do i1=mrho,nrho
jj=jj+i1*rho(i1)
do i2=1,rho(i1)
n=n+1
vdeg(n)=i1
end do
end do
nli=jj/2
loop=nli-n+1
serrt=qerrty%ok
if(n.gt.maxn)then
serrt=qerrty%q
else if(loop.ne.nloop)then
serrt=qerrty%q
else if(jj.ne.nli+nli)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='qg21_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
rhop2=rho(-1)+loop
if(dflag(dflaty%edge).lt.0)then
if(nli.gt.rho(-1))then
qcntrx=qcntr%p
jflag(jflaty%nogp)=1
go to 27
end if
else if(dflag(dflaty%edge).gt.0)then
if(nli.lt.rhop1)then
qcntrx=qcntr%p
jflag(jflaty%nogp)=1
go to 27
end if
end if
j1=0
if(dflag(dflaty%nodl).gt.0)then
j1=1
else if(dflag(dflaty%nopa).gt.0)then
j1=1
else if(dflag(dflaty%simp).gt.0)then
j1=1
end if
do i1=rhop1,n
if(j1.ne.0)then
str(i1)=1
else if(vdeg(i1).ne.vdeg(n))then
str(i1)=min(vdeg(i1),loop+1)
else if(n.gt.2)then
str(i1)=min(vdeg(i1)-1,loop+1)
else
str(i1)=min(vdeg(i1),loop+1)
end if
end do
j1=1
xl(1)=1
do i1=2,n
if(vdeg(i1).ne.vdeg(i1-1))then
xt(j1)=i1-1
j1=j1+1
xl(j1)=i1
end if
end do
xt(j1)=n
if(n.gt.0)then
xn(1:n)=0
end if
if(rho(-1).eq.0)then
xc(1)=0
go to 59
end if
kk=0
n1=1
do i1=mrho,nrho
if(rho(i1).gt.0)then
n1=n1+1
degr(n1)=i1
bound(n1)=i1*rho(i1)
kk=kk+bound(n1)
end if
end do
xc(1)=max(0,rho(-1)-kk)
61 continue
ii=rho(-1)-xc(1)
do i1=n1,2,-1
xc(i1)=min(ii,bound(i1))
ii=ii-xc(i1)
end do
43 continue
do i1=n1,2,-1
ii=xc(i1)
do i2=xl(i1),xt(i1)
xn(i2)=min(ii,degr(i1))
ii=ii-xn(i2)
xs(i2)=ii
end do
end do
go to 12
76 continue
d01: do i1=n1,2,-1
do i2=xt(i1)-1,xl(i1),-1
if(xn(i2).gt.1)then
j1=i2
go to 89
end if
end do
cycle d01
89 continue
xn(j1)=xn(j1)-1
xs(j1)=xs(j1)+1
do i2=j1+1,xt(i1)
xn(i2)=min(xn(j1),xs(i2-1))
xs(i2)=xs(i2-1)-xn(i2)
end do
if(xs(xt(i1)).gt.0)then
do i2=j1-1,xl(i1),-1
if(xn(i2).gt.1)then
j1=i2
go to 89
end if
end do
cycle d01
end if
do i2=i1+1,n1
ii=xc(i2)
do i3=xl(i2),xt(i2)
xn(i3)=min(ii,degr(i2))
ii=ii-xn(i3)
xs(i3)=ii
end do
end do
go to 12
end do d01
do i1=n1,3,-1
if(xc(i1).gt.0)then
j1=i1
go to 45
end if
end do
go to 85
45 continue
do i1=j1-1,2,-1
if(xc(i1).lt.bound(i1))then
j1=i1
go to 55
end if
end do
go to 85
55 continue
xc(j1)=xc(j1)+1
ii=-1
do i1=j1+1,n1
ii=ii+xc(i1)
end do
do i1=n1,j1+1,-1
xc(i1)=min(ii,bound(i1))
ii=ii-xc(i1)
end do
if(ii.ne.0)then
qerrmsg(1:srec)='qg21_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
go to 43
85 continue
xc(1)=xc(1)+2
if(xc(1).le.rho(-1))then
go to 61
end if
qcntrx=qcntr%p
go to 27
12 continue
if(rho(-1).lt.n)then
if(xc(1).gt.0)then
qcntrx=qcntr%p
go to 27
end if
end if
if(n.gt.rhop1)then
j1=0
if(dflag(dflaty%nob).gt.0)then
j1=1
end if
do i1=rhop1,n
if(xn(i1)+j1.ge.vdeg(i1))then
go to 76
end if
end do
end if
if(nrho.gt.mrho)then
if(mflag(mflaty%one).eq.0)then
do i1=1,rho(-1)
if(stib(efinvdc(0)+i1).gt.0)then
j1=stib(link(0)+stib(leg(0)+i1))
j2=0
do i2=rhop1,n
if(xn(i2).gt.0)then
j2=j2+min(xn(i2),stib(stib(efinvdc(0)+i1)+vdeg(i2)))
end if
end do
if(j2.lt.stib(efm(0)+i1))then
go to 76
end if
end if
end do
end if
end if
ii=1
if(loop.eq.0)then
ii=0
else if(dflag(dflaty%bip).gt.0)then
ii=0
else if(dflag(dflaty%nosl).gt.0)then
ii=0
else if(dflag(dflaty%edge).lt.0)then
ii=0
else if(dflag(dflaty%simp).gt.0)then
ii=0
else
if(dflag(dflaty%nosn).gt.0)then
if(rho(-1)-1.ne.0)then
ii=0
end if
end if
if(dflag(dflaty%cyc).gt.0)then
if(loop-1.ne.0)then
ii=0
end if
end if
end if
if(ii.eq.0)then
do i1=rhop1,n
dta(i1)=0
end do
else
do i1=rhop1,n
ii=0
if(n.gt.rhop1)then
if(dflag(dflaty%nob).gt.0)then
ii=2
else if((dflag(dflaty%nosb).gt.0).and.&
(xn(i1).eq.0))then
ii=2
else
ii=1
end if
end if
jj=max(0,min(vdeg(i1)-xn(i1)-ii,loop+loop))/2
dta(i1)=jj+jj
if(dflag(dflaty%nopa).gt.0)then
dta(i1)=min(dta(i1),2)
end if
end do
end if
59 continue
do i1=1,n-1
xg(i1,i1+1:n)=0
end do
do i1=2,xc(1),2
xg(i1-1,i1)=1
end do
limin=rhop1
limax=max(limin,n-1)
lin=limin
j1=xc(1)
do i1=limin,n
if(xn(i1).gt.0)then
a1(i1)=j1+1
do i2=1,xn(i1)
j1=j1+1
xg(j1,i1)=1
vmap(j1,1)=i1
end do
else
a1(i1)=0
end if
end do
dsum=-1
70 continue
dsum=dsum+1
if(dsum.gt.loop)then
go to 76
end if
ii=2*dsum
do i1=n,rhop1,-1
jj=min(ii,dta(i1))
xg(i1,i1)=jj
ii=ii-jj
end do
if(ii.eq.0)then
go to 19
else
go to 76
end if
32 continue
do i1=n,rhop1,-1
if(xg(i1,i1).gt.0)then
j1=i1
go to 33
end if
end do
go to 70
33 continue
do i1=j1-1,rhop1,-1
if(xg(i1,i1).lt.dta(i1))then
xg(i1,i1)=xg(i1,i1)+2
j2=i1
go to 65
end if
end do
go to 70
65 continue
ii=-2
do i1=j2+1,j1
ii=ii+xg(i1,i1)
end do
do i1=n,j2+1,-1
jj=min(ii,dta(i1))
xg(i1,i1)=jj
ii=ii-jj
end do
if(ii.ne.0)then
qerrmsg(1:srec)='qg21_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
19 continue
do i1=limin,n
ds(limin,i1)=vdeg(i1)-xn(i1)-xg(i1,i1)
end do
uset(0)=0
xset(1)=1
jj=1
do i1=2,n
if(vdeg(i1-1).ne.vdeg(i1))then
uset(jj)=i1-1
jj=jj+1
else if(xn(i1-1).ne.xn(i1))then
uset(jj)=i1-1
jj=jj+1
else
ii=xg(i1-1,i1-1)-xg(i1,i1)
if(ii.gt.0)then
uset(jj)=i1-1
jj=jj+1
else if(ii.lt.0)then
go to 32
end if
end if
xset(i1)=jj
end do
uset(jj)=n
lps(lin)=loop-dsum+1
10 continue
ii=ds(lin,lin)
bond=min(str(lin),lps(lin))
do i1=n,lin+1,-1
jj=min(ii,bond,ds(lin,i1))
xg(lin,i1)=jj
ii=ii-jj
end do
if(ii.gt.0)then
go to 15
end if
go to 28
05 continue
lin=limax
go to 17
15 continue
if(lin.eq.limin)then
go to 32
end if
lin=lin-1
17 continue
if((lin.lt.limin).or.&
(lin.gt.n))then
qerrmsg(1:srec)='qg21_5'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
do col=n,lin+1,-1
aux=xg(lin,col)-1
if(aux.ge.0)then
go to 23
end if
end do
go to 15
23 continue
bond=min(str(lin),lps(lin))
do i1=col-1,lin+1,-1
if(min(ds(lin,i1),bond).gt.xg(lin,i1))then
xg(lin,i1)=xg(lin,i1)+1
do i2=n,i1+1,-1
xg(lin,i2)=min(aux,bond,ds(lin,i2))
aux=aux-xg(lin,i2)
end do
go to 28
end if
aux=aux+xg(lin,i1)
end do
go to 15
38 continue
aux=-1
do i1=col,n
aux=aux+xg(lin,i1)
end do
go to 23
28 continue
if(lin.eq.n)then
go to 200
end if
msum=0
do i1=lin+1,n
ii=xg(lin,i1)-1
if(ii.gt.0)then
msum=msum+ii
end if
end do
if(msum.ge.lps(lin))then
go to 17
end if
if(lin.gt.limin)then
if(xset(lin).eq.xset(lin-1))then
do i1=limin,lin-2
ii=xg(i1,lin-1)-xg(i1,lin)
if(ii.gt.0)then
go to 35
else if(ii.lt.0)then
qerrmsg(1:srec)='qg21_7'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
do col=lin+1,n
ii=xg(lin-1,col)-xg(lin,col)
if(ii.lt.0)then
go to 38
else if(ii.gt.0)then
go to 35
end if
end do
end if
end if
35 continue
do col=lin+2,n
if(xset(col).eq.xset(col-1))then
do i1=limin,lin
ii=xg(i1,col-1)-xg(i1,col)
if(ii.lt.0)then
go to 38
else if(ii.gt.0)then
exit
end if
end do
end if
end do
do i1=lin+1,n
ds(lin+1,i1)=ds(lin,i1)-xg(lin,i1)
if(ds(lin+1,i1).lt.0)then
qerrmsg(1:srec)='qg21_8'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
lin=lin+1
lps(lin)=lps(lin-1)-msum
go to 10
200 continue
if(dflag(dflaty%nosl).lt.0)then
do i1=n,rhop1,-1
if(xg(i1,i1).gt.0)then
go to 210
end if
end do
go to 05
end if
210 continue
if(dflag(dflaty%nodl).lt.0)then
do i1=n-1,rhop1,-1
do i2=i1+1,n
if(xg(i1,i2)-1.gt.0)then
go to 220
end if
end do
end do
go to 05
end if
220 continue
j1=rhop1
j2=n-1
lin=n
do i1=j1,j2
aa(i1)=0
end do
aa(n)=1
i1=n-rho(-1)
bb(i1)=lin
kk=i1-1
21 continue
if(kk.gt.0)then
ii=bb(i1)
i1=i1-1
do i2=j2,ii+1,-1
if(aa(i2).eq.0)then
if(xg(ii,i2).ne.0)then
bb(kk)=i2
kk=kk-1
aa(i2)=-aa(ii)
end if
end if
end do
if(aa(j2).ne.0)then
j2=j2-1
end if
do i2=j1,ii-1
if(aa(i2).eq.0)then
if(xg(i2,ii).ne.0)then
bb(kk)=i2
kk=kk-1
aa(i2)=-aa(ii)
end if
end if
end do
if(aa(j1).ne.0)then
j1=j1+1
end if
if(i1.eq.kk)then
do i2=j2,j1,-1
if(aa(i2).eq.0)then
aa(i2)=1
bb(kk)=i2
kk=kk-1
lin=i2
j2=lin-1
go to 21
end if
end do
qerrmsg(1:srec)='qg21_9'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
go to 21
end if
if(lin.ne.n)then
go to 17
end if
if(dflag(dflaty%bip).ne.0)then
do i1=rhop1,n
if(xg(i1,i1).ne.0)then
if(dflag(dflaty%bip).gt.0)then
go to 05
else
go to 230
end if
end if
do i2=i1+1,n
if(xg(i1,i2).ne.0)then
if(aa(i1)+aa(i2).ne.0)then
if(dflag(dflaty%bip).gt.0)then
go to 05
else
go to 230
end if
end if
end if
end do
end do
if(dflag(dflaty%bip).lt.0)then
go to 05
end if
end if
230 continue
if(dflag(dflaty%nopa).lt.0)then
do i1=n,rhop1,-1
if(xg(i1,i1)-3.gt.0)then
go to 240
end if
do i2=i1+1,n
if(xg(i1,i2)-1.gt.0)then
go to 240
end if
end do
end do
go to 05
end if
240 continue
if(dflag(dflaty%simp).lt.0)then
do i1=n,rhop1,-1
do i2=i1,n
if(xg(i1,i2)-1.gt.0)then
go to 250
end if
end do
end do
go to 05
end if
250 continue
do i1=1,n
do i2=1,i1-1
j1=xg(i2,i1)
gam(i1,i2)=j1
gam(i2,i1)=j1
end do
gam(i1,i1)=xg(i1,i1)
end do
if(dflag(dflaty%nob).ne.0)then
call qumpi(1,ii)
Q_ERRT
if(ii.ne.dflag(dflaty%nob))then
go to 05
end if
end if
if(dflag(dflaty%nosb).ne.0)then
call qumpi(2,ii)
Q_ERRT
if(ii.ne.dflag(dflaty%nosb))then
go to 05
end if
end if
if(dflag(dflaty%onsh).ne.0)then
call qumpi(4,ii)
Q_ERRT
if(ii.ne.dflag(dflaty%onsh))then
go to 05
end if
end if
if(dflag(dflaty%onshx).ne.0)then
call qumvi(3,ii)
Q_ERRT
if(ii.ne.dflag(dflaty%onshx))then
go to 05
end if
end if
if(dflag(dflaty%nosn).ne.0)then
if(rho(-1).ne.1)then
call qumvi(1,ii)
Q_ERRT
else
call qumvi(3,ii)
Q_ERRT
end if
if(ii.ne.dflag(dflaty%nosn))then
go to 05
end if
end if
if(dflag(dflaty%ovi).ne.0)then
call qumvi(2,ii)
Q_ERRT
if(ii.ne.dflag(dflaty%ovi))then
go to 05
end if
end if
ntadp=0
if(mflag(mflaty%notadp).ne.0)then
call qumpi(3,ii)
Q_ERRT
if(ii.ne.1)then
qerrmsg(1:srec)='qg21_11'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
ngsym=0
do i1=1,rho(-1)-1
p1s(i1,i1+1:rho(-1))=0
end do
do i1=1,n
xp(i1)=i1
end do
go to 93
77 continue
do i1=xset(n),1,-1
do i2=uset(i1)-1,uset(i1-1)+1,-1
if(xp(i2).lt.xp(i2+1))then
go to 102
end if
end do
end do
go to 63
102 continue
j1=uset(i1)
do i1=i2+2,j1
if(xp(i1).lt.xp(i2))then
go to 202
end if
end do
i1=j1+1
202 continue
i1=i1-1
ii=xp(i1)
xp(i1)=xp(i2)
xp(i2)=ii
i1=i2+1
i2=j1
204 continue
if(i1.lt.i2)then
ii=xp(i1)
xp(i1)=xp(i2)
xp(i2)=ii
i1=i1+1
i2=i2-1
go to 204
end if
do i1=j1+1,n
xp(i1)=i1
end do
93 continue
if(rho(-1).gt.0)then
if(xp(rho(-1)).ne.rho(-1))then
go to 63
end if
end if
do i1=rhop1,n-1
do i2=i1,n
ii=gam(xp(i1),xp(i2))-gam(i1,i2)
if(ii.gt.0)then
go to 05
end if
if(ii.lt.0)then
j1=xset(i2)
j3=uset(j1)
do i3=i2+1,j3-1
do i4=i3+1,j3
if(xp(i3).lt.xp(i4))then
ii=xp(i3)
xp(i3)=xp(i4)
xp(i4)=ii
end if
end do
end do
do i3=j1+1,xset(n)
j2=j3+1
j3=uset(i3)
j4=j2+j3
do i4=j2,j3
xp(i4)=j4-i4
end do
end do
go to 77
end if
end do
end do
if(rho(-1).eq.0)then
go to 114
end if
i1=1
110 continue
j1=vmap(i1,1)
if(xp(j1).eq.j1)then
i1=i1+xn(j1)
if(i1.le.rho(-1))then
go to 110
end if
go to 114
else
p1s(i1,a1(xp(j1)))=1
go to 77
end if
114 continue
if(jflag(jflaty%noaut).eq.0)then
if(psym(0).lt.0)then
psyms=0
psym(0)=stibs(1)
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
end if
jj=n-rho(-1)
ii=ngsym*jj-psyms
if(ii.gt.0)then
if(psym(0).eq.stibs(1)-1-psyms)then
call qaoib(ii)
Q_ERRT
psyms=psyms+ii
stib(stibs(1))=eoa
else
qerrmsg(1:srec)='qg21_13'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
ii=ngsym*jj
if(ii.le.psyms)then
if(ngsym.gt.0)then
ii=psym(0)+(ii-n)
do i1=rhop1,n
stib(ii+i1)=xp(i1)
end do
end if
else
qerrmsg(1:srec)='qg21_14'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
ngsym=ngsym+1
go to 77
63 continue
ns1=0
do i1=2,rho(-1)
j1=i1-1
if(vmap(j1,1).eq.vmap(i1,1))then
p1s(j1,i1)=1
end if
do i2=1,j1
if(p1s(i2,i1).eq.1)then
ns1=ns1+1
p1l(ns1)=i2
p1r(ns1)=i1
end if
end do
end do
if(cflag(confi%qlist).eq.0)then
if(jflag(jflaty%intlp).eq.0)then
go to 57
end if
end if
do i1=1,rho(-1)
tail(i1)=i1
head(i1)=vmap(i1,1)
end do
if(vdeg(n).gt.0)then
nemul(1:vdeg(n))=0
end if
ii=rhop1
do i1=rhop1,n
do i2=i1,n
jj=gam(i1,i2)
if(jj.eq.0)then
ege(i1,i2)=0
else
ege(i1,i2)=ii
if(i1.eq.i2)then
jj=jj/2
else
nemul(jj)=nemul(jj)+1
emul(jj,nemul(jj))=ii
end if
ii=ii+jj
do i3=ii-jj,ii-1
tail(i3)=i1
head(i3)=i2
end do
end if
end do
end do
if(jflag(jflaty%intlp).eq.0)then
go to 57
end if
do i1=rhop1,nli
intree(i1)=0
end do
if(n.gt.0)then
bb(1:n)=0
end if
do i1=rhop1,n
aa(i1)=0
end do
kk=0
ntree=0
ii=vdeg(n)
51 continue
if(ii.le.0)then
go to 52
end if
jj=nemul(ii)
58 continue
if(jj.le.0)then
ii=ii-1
go to 51
end if
j1=tail(emul(ii,jj))
j2=head(emul(ii,jj))
if(aa(j1).eq.aa(j2))then
if(aa(j1).eq.0)then
ntree=ntree+1
aa(j1)=ntree
aa(j2)=ntree
else
jj=jj-1
go to 58
end if
else
if(aa(j1).eq.0)then
aa(j1)=aa(j2)
else if(aa(j2).eq.0)then
aa(j2)=aa(j1)
else
j3=aa(j2)
do i1=rhop1,n
if(aa(i1).eq.j3)then
aa(i1)=aa(j1)
end if
end do
end if
end if
intree(ege(j1,j2))=1
bb(j1)=bb(j1)+1
bb(j2)=bb(j2)+1
kk=kk+1
if(kk.lt.n-rhop1)then
jj=jj-1
go to 58
end if
52 continue
do i1=1,rho(-1)
intree(i1)=1
end do
do i1=1,nli
do i2=1,rhop2
flow(i1,i2)=0
end do
end do
do i1=1,rho(-1)
flow(i1,i1)=1
end do
ii=rho(-1)
do i1=rhop1,nli
if(intree(i1).eq.0)then
ii=ii+1
flow(i1,ii)=1
end if
end do
ii=rhop1
73 continue
if(bb(ii).eq.1)then
go to 71
else if(ii.lt.n)then
ii=ii+1
go to 73
else
go to 83
end if
71 continue
do i1=rhop1,ii-1
if(xg(i1,ii).ne.0)then
j1=ege(i1,ii)
if(intree(j1).ne.0)then
go to 75
end if
end if
end do
do i1=ii+1,n
if(xg(ii,i1).ne.0)then
j1=ege(ii,i1)
if(intree(j1).ne.0)then
go to 75
end if
end if
end do
qerrmsg(1:srec)='qg21_16'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
75 continue
if(rho(-1).gt.1)then
if(xn(ii).gt.0)then
do i1=1,rho(-1)
if(vmap(i1,1).eq.ii)then
if(tail(j1).eq.ii)then
flow(j1,i1)=flow(j1,i1)+1
else
flow(j1,i1)=flow(j1,i1)-1
end if
end if
end do
end if
end if
do i1=rhop1,n
if(i1.ne.ii)then
if(i1.lt.ii)then
jj=ege(i1,ii)
else
jj=ege(ii,i1)
end if
do i2=jj,jj+gam(ii,i1)-1
if(intree(i2).eq.0)then
if((head(j1).eq.head(i2)).or.&
(tail(j1).eq.tail(i2)))then
do i3=1,rhop2
flow(j1,i3)=flow(j1,i3)-flow(i2,i3)
end do
else
do i3=1,rhop2
flow(j1,i3)=flow(j1,i3)+flow(i2,i3)
end do
end if
end if
end do
end if
end do
intree(j1)=0
bb(tail(j1))=bb(tail(j1))-1
bb(head(j1))=bb(head(j1))-1
ii=rhop1
go to 73
83 continue
do i1=rhop1,nli
ii=0
jj=0
do i2=1,rho(-1)
kk=flow(i1,i2)
if(kk.gt.0)then
ii=ii+1
else if(kk.lt.0)then
jj=jj+1
end if
end do
if((ii.gt.0).and.&
(jj.gt.0))then
qerrmsg(1:srec)='qg21_17'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(2*(ii+jj).gt.rho(-1))then
if(jj.eq.0)then
do i2=1,rho(-1)
flow(i1,i2)=flow(i1,i2)-1
end do
else
do i2=1,rho(-1)
flow(i1,i2)=flow(i1,i2)+1
end do
end if
end if
end do
do i1=1,nli
do i2=1,rhop2
if(abs(flow(i1,i2)).gt.1)then
qerrmsg(1:srec)='qg21_18'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
end do
net(:)=0
d02: do i1=rhop1,nli
do i2=rhop1,rhop2
if(flow(i1,i2).ne.0)then
if(head(i1).ne.tail(i1))then
kk=edgty%rnb
else
kk=edgty%snb
end if
flow(i1,0)=kk
net(kk)=net(kk)+1
cycle d02
end if
end do
do i2=1,rho(-1)
if(flow(i1,i2).ne.0)then
if(dflag(dflaty%norb).gt.0)then
go to 05
end if
flow(i1,0)=edgty%rb
net(1)=net(1)+1
cycle d02
end if
end do
net(2)=net(2)+1
flow(i1,0)=edgty%sb
end do d02
net(3)=net(1)+net(2)
net(-3)=net(-1)+net(-2)
net(0)=net(-3)+net(3)
ii=-2*net(-2)
do i1=rhop1,n
ii=ii+gam(i1,i1)
end do
if(ii.ne.0)then
qerrmsg(1:srec)='qg21_123'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(dflag(dflaty%norb).lt.0)then
if(net(1).eq.0)then
go to 05
end if
end if
if(zbri(net(3)).le.0)then
go to 05
else if(zcho(net(-3)).le.0)then
go to 05
else if(rbri(net(1)).le.0)then
go to 05
else if(sbri(net(2)).le.0)then
go to 05
end if
if(dflag(dflaty%nosig).ne.0)then
call qgsig(ii,head,tail)
Q_ERRT
if(dflag(dflaty%nosig).ne.ii)then
go to 05
end if
end if
do i1=1,rho(-1)
ege(i1,vmap(i1,1))=i1
end do
do i1=rhop1,n
ii=0
do i2=1,rho(-1)
jj=0
do i3=1,n
if(i3.ne.i1)then
j2=gam(i1,i3)
if(j2.gt.0)then
if(i1.lt.i3)then
j1=ege(i1,i3)
else
j1=ege(i3,i1)
end if
j3=head(j1)-i1
do i4=j1,j1+j2-1
if(j3.eq.0)then
jj=jj+flow(i4,i2)
else
jj=jj-flow(i4,i2)
end if
end do
end if
end if
end do
if(jj.ne.ii)then
if(i2.eq.1)then
ii=jj
else
qerrmsg(1:srec)='qg21_19'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
end do
end do
do i1=rhop1,n
do i2=rhop1,rhop2
ii=0
do i3=1,n
if(i3.ne.i1)then
j2=gam(i1,i3)
if(j2.gt.0)then
if(i1.lt.i3)then
j1=ege(i1,i3)
else
j1=ege(i3,i1)
end if
j3=head(j1)-i1
do i4=j1,j1+j2-1
if(j3.eq.0)then
ii=ii+flow(i4,i2)
else
ii=ii-flow(i4,i2)
end if
end do
end if
end if
end do
if(ii.ne.0)then
qerrmsg(1:srec)='qg21_20'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
end do
57 continue
qco(qcntr%t)=1
99 continue
return
end subroutine qg21
subroutine qgsig(situ,head,tail)
use,non_intrinsic::qkeys
use,non_intrinsic::qmix
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::head(1:maxli),tail(1:maxli)
integer(kind=c_int_least32_t),intent(out)::situ
integer(kind=c_int_least32_t)::aa(1:maxli),bb(1:maxli)
integer(kind=c_int_least32_t)::ii,jj,rr,ss,tt
integer(kind=c_int_least32_t)::f1,i1,i2,i3,i4,j3,j4
situ=1
if(rho(-1).eq.0)then
go to 80
end if
do i1=rhop1,nli
f1=flow(i1,0)
if(abs(f1).eq.edgty%re)then
do i2=1,i1-1
ii=1
if(i2.lt.rhop1)then
if(f1.eq.edgty%rb)then
ii=0
end if
else if(f1.eq.flow(i2,0))then
ii=0
end if
if(ii.eq.0)then
do i3=-1,1,2
if(f1.lt.0)then
do i4=rhop1,rhop2
ii=flow(i1,i4)+i3*flow(i2,i4)
if(ii.ne.0)then
go to 10
end if
end do
end if
ii=0
jj=0
do i4=1,rho(-1)
if(flow(i1,i4)+i3*flow(i2,i4).ne.0)then
if(jj.ne.0)then
go to 10
end if
ii=ii+1
else
if(ii.ne.0)then
go to 10
end if
jj=jj+1
end if
end do
go to 80
10 continue
end do
end if
end do
end if
end do
if(rho(-1)-1.ne.0)then
if(net(2)-1.le.0)then
go to 99
end if
else
if(net(2).ne.0)then
go to 80
else
go to 99
end if
end if
rr=0
do i3=rhop1,n
if(xn(i3).eq.0)then
aa(i3)=0
else
aa(i3)=1
rr=rr+1
bb(rr)=i3
end if
end do
if(rr.le.0)then
qerrmsg(1:srec)='qgsig_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ss=1
30 continue
tt=bb(ss)
do i3=rhop1,n
if(aa(i3).eq.0)then
if(i3.ne.tt)then
if(i3.lt.tt)then
j3=i3
j4=tt
else
j3=tt
j4=i3
end if
if(gam(j3,j4).ne.0)then
if(flow(ege(j3,j4),0).ne.edgty%sb)then
aa(i3)=1
rr=rr+1
bb(rr)=i3
end if
end if
end if
end if
end do
if(ss.lt.rr)then
ss=ss+1
go to 30
end if
do i1=rhop1,nli
if(flow(i1,0).eq.edgty%sb)then
if(aa(head(i1)).eq.0)then
if(aa(tail(i1)).eq.0)then
go to 80
end if
end if
end if
end do
go to 99
80 continue
situ=-1
99 continue
return
end subroutine qgsig
subroutine qgen
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
#ifdef Q_API
use,non_intrinsic::q_api
#endif
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstoz,qbprod
integer(kind=c_int_least32_t)::i,ii,ij,ik,i1,i2,i3,i4,i5,j,jj,jk,j1,j2,j3,j4,k,kk
integer(kind=c_int_least32_t)::a1,a2,aux,b1,b2,igo,jgo
integer(kind=c_int_least32_t)::aoff,atyp,ktyp,narg,styp,vi,vind,vj,vk,vv
integer(kind=c_int_least32_t)::xli(qb2)
if(qsgnl.ne.0)then
if(qsgnl.ne.1)then
qerrt(0)=qerrty%q
call qstop
Q_ERRT
end if
end if
#ifdef Q_API
if(qxmod.eq.qmod%api)then
if(qpsgnl.eq.qisgnl%hold)then
go to 505
end if
end if
#endif
serrt=qerrty%ok
outd(qcntr%d)=0
qco(qcntr%d)=0
qsgnl=0
if(jflag(jflaty%ingg).eq.0)then
outd(:)=0
qco(:)=[0,1,1,1,1]
qcntrx=qcntr%c
jflag(jflaty%ingg)=1
cflag(confi%nontlf)=cflag(confi%nontnls)
else
qco(:)=[0,0,0,0,0]
if(dflag(dflaty%newc).ne.0)then
qcntrx=qcntr%c
else if(dflag(dflaty%newp).ne.0)then
qcntrx=qcntr%p
else if(dflag(dflaty%newt).ne.0)then
qcntrx=qcntr%t
else if(dflag(dflaty%newe).ne.0)then
qcntrx=qcntr%e
else
qcntrx=qcntr%d
end if
if(cflag(confi%maxc).gt.0)then
if(qcol(dcoty%maxc).eq.qcol(dcoty%nat))then
if(stcb(qcop(dcoty%maxc)+1:qcop(dcoty%maxc)+qcol(dcoty%maxc)).eq.&
stcb(qcop(dcoty%nat)+1:qcop(dcoty%nat)+qcol(dcoty%nat)))then
cflag(confi%maxc)=-1
qcntrx=qcntr%p
end if
end if
end if
end if
if(qcntrx.lt.qcntr%e)then
go to 58
end if
27 continue
if(qcntrx.lt.qcntr%e)then
qcntrx=qcntr%e
end if
call qg10
Q_ERRT
if(qco(qcntr%e).eq.0)then
qerrt(0)=qerrty%qend
if(qxmod.eq.qmod%auto)then
call qende
Q_ERRT
end if
go to 99
end if
do i1=1,rho(-1)
j1=stib(leg(0)+ps1(i1))
pmap(i1,1)=j1
pmap(vmap(i1,1),lmap(i1,1))=stib(link(0)+j1)
end do
vind=rho(-1)
57 continue
vind=vind+1
vv=vlis(vind)
vfo(vv)=stib(stib(dpntro(0)+vdeg(vv))+pmap(vv,1))
100 continue
do i1=1,rdeg(vv)
ii=stib(vfo(vv)+i1)-pmap(vv,i1)
if(ii.lt.0)then
vfo(vv)=vfo(vv)+vdeg(vv)+1
go to 100
else if(ii.gt.0)then
go to 104
end if
end do
go to 163
104 continue
if(vind.ne.rhop1)then
vind=vind-1
vv=vlis(vind)
go to 58
end if
go to 27
58 continue
vfo(vv)=vfo(vv)+vdeg(vv)+1
do i1=rdeg(vv),1,-1
if(stib(vfo(vv)+i1).ne.pmap(vv,i1))then
go to 104
end if
end do
163 continue
if(jflag(jflaty%vexc).ne.0)then
if(stib(vsfi(0)+stib(vfo(vv))).ne.0)then
go to 58
end if
end if
do i1=rdeg(vv)+1,sdeg(vv),2
j1=vfo(vv)+i1
j2=stib(j1)
j3=stib(j1+1)
if(j2.gt.j3)then
go to 58
else if(j2.ne.stib(link(0)+j3))then
go to 58
else if(i1+1.ne.sdeg(vv))then
if(j2.gt.stib(j1+2))then
go to 58
end if
end if
end do
if(jflag(jflaty%pexc).eq.0)then
do i1=rdeg(vv)+1,vdeg(vv)
pmap(vv,i1)=stib(vfo(vv)+i1)
end do
else
do i1=rdeg(vv)+1,vdeg(vv)
j1=stib(vfo(vv)+i1)
if(stib(psfi(0)+j1).ne.0)then
go to 58
end if
pmap(vv,i1)=j1
end do
end if
do i1=sdeg(vv)+1,vdeg(vv)-1
if(vmap(vv,i1).eq.vmap(vv,i1+1))then
if(pmap(vv,i1).gt.pmap(vv,i1+1))then
go to 58
end if
end if
end do
if(mflag(mflaty%ext).ne.0)then
do i1=rdeg(vv)+1,vdeg(vv)
if(stib(tpc(0)+pmap(vv,i1)).eq.phity%ext)then
go to 58
end if
end do
end if
if(mflag(mflaty%notadp).ne.0)then
do i1=1,ntadp
if(xtail(i1).eq.vv)then
jj=xhead(i1)
else if(xhead(i1).eq.vv)then
jj=xtail(i1)
else
jj=0
end if
if(jj.ne.0)then
do i2=1,vdeg(vv)
if(jj.eq.vmap(vv,i2))then
if(stib(tpc(0)+pmap(vv,i2)).eq.phity%notdp)then
go to 58
end if
end if
end do
end if
end do
end if
do i1=sdeg(vv)+1,vdeg(vv)
pmap(vmap(vv,i1),lmap(vv,i1))=stib(link(0)+pmap(vv,i1))
end do
if(vind.lt.n)then
go to 57
end if
if(dflag(dflaty%fl).eq.0)then
go to 333
end if
if(nloop.eq.0)then
if(dflag(dflaty%fl).gt.0)then
go to 333
else if(dflag(dflaty%fl).lt.0)then
go to 58
end if
end if
if(n.gt.0)then
xli(1:n)=0
end if
do i1=1,n
if(xli(i1).eq.0)then
ii=i1
kk=1
820 continue
do i2=1,vdeg(ii)
if(i2.ne.xli(ii))then
jj=pmap(ii,i2)
if(stib(antiq(0)+jj).ne.0)then
k=ii
ii=vmap(k,i2)
xli(ii)=lmap(k,i2)
if(ii.gt.rho(-1))then
if(ii.ne.i1)then
kk=-kk
go to 820
end if
if(kk.gt.0)then
if(dflag(dflaty%fl).gt.0)then
go to 58
else
go to 333
end if
end if
end if
exit
end if
end if
end do
end if
end do
if(dflag(dflaty%fl).lt.0)then
go to 58
end if
333 continue
if(jflag(jflaty%noaut).ne.0)then
ndsym(symt%nl)=ngsym
else
ndsym(symt%nl)=1
jk=psym(0)-rho(-1)
do i1=2,ngsym
if(mflag(mflaty%one).eq.0)then
do i2=rhop1,n
j1=stib(jk+i2)
j2=rdeg(i2)+1
400 continue
if(j2.le.vdeg(i2))then
j3=vmap(i2,j2)
j4=1
410 continue
if(j4.le.vdeg(i2))then
if(vmap(j1,j4).ne.stib(jk+j3))then
j4=j4+1
go to 410
end if
end if
jj=gam(i2,j3)
do i3=1,jj
xli(i3)=pmap(j1,i3+j4-1)
end do
do i3=1,jj-1
do i4=i3+1,jj
if(xli(i3).gt.xli(i4))then
ii=xli(i3)
xli(i3)=xli(i4)
xli(i4)=ii
end if
end do
end do
do i3=1,jj
ii=xli(i3)-pmap(i2,j2)
if(ii.lt.0)then
go to 58
else if(ii.gt.0)then
go to 339
end if
j2=j2+1
end do
go to 400
end if
end do
end if
if(mflag(mflaty%vdup).ne.0)then
do i2=rhop1,n
j1=stib(jk+i2)
if(i2.ne.j1)then
ii=stib(vfo(j1))-stib(vfo(i2))
if(ii.lt.0)then
go to 58
else if(ii.gt.0)then
go to 339
end if
end if
end do
end if
ndsym(symt%nl)=ndsym(symt%nl)+1
339 continue
jk=jk+(n-rho(-1))
end do
end if
if(dflag(dflaty%vsum).ne.0)then
jgo=0
vi=n
atyp=opety%vsum
j1=stib(tftic(0)+atyp)
do i1=stib(tfta(0)+j1),stib(tftb(0)+j1)
i2=stib(tf2(0)+i1)
styp=stib(tftyp(0)+i2)
aoff=stib(tfo(0)+i2)
j3=stib(aoff+1)
jj=stib(vmkzp(0)+j3)
ii=0
do k=rhop1,n
ii=ii+stib(jj+stib(vfo(k)))
end do
j1=stib(tfa(0)+i2)
j2=stib(tfb(0)+i2)
igo=0
if(styp.gt.0)then
if((ii.lt.j1).or.&
(ii.gt.j2))then
igo=1
end if
else
if((ii.ge.j1).and.&
(ii.le.j2))then
igo=1
end if
end if
if(igo.ne.0)then
jgo=1
a1=stib(vmkmio(0)+j3)
b1=stib(vmkmao(0)+j3)
a2=stib(stib(tfills(0)+i2)+rhop1)
b2=stib(stib(tfiuls(0)+i2)+rhop1)
if(styp.gt.0)then
do i3=rhop1,n-1
i4=vlis(i3)
i5=stib(jj+stib(vfo(i4)))
i4=vdeg(i4)
a2=a2+(i5-stib(b1+i4))
b2=b2+(i5-stib(a1+i4))
if((a2.lt.0).or.&
(b2.gt.0))then
if(vi.gt.i3)then
vi=i3
vj=jj
vk=i5
end if
exit
end if
end do
else
do i3=rhop1,n-1
i4=vlis(i3)
i5=stib(jj+stib(vfo(i4)))
i4=vdeg(i4)
a2=a2+(i5-stib(a1+i4))
b2=b2+(i5-stib(b1+i4))
if((a2.ge.0).and.&
(b2.le.0))then
if(vi.gt.i3)then
vi=i3
vj=jj
vk=i5
end if
exit
end if
end do
end if
end if
end do
if(jgo.ne.0)then
if(vi.lt.n)then
vind=vi
vv=vlis(vind)
end if
go to 58
end if
end if
do i1=1,ntf
narg=stib(tfnarg(0)+i1)
styp=stib(tftyp(0)+i1)
atyp=abs(styp)
ktyp=0
do i2=1,ncopt2
if(stib(copt2(0)+i2).eq.atyp)then
ktyp=stib(xopt2(0)+i2)
exit
end if
end do
if(ktyp.eq.0)then
qerrmsg(1:srec)='qgen_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if((narg.eq.0).and.&
(atyp.eq.0))then
cycle
else if((narg.le.0).or.&
(atyp.le.0))then
qerrmsg(1:srec)='qgen_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
else if(atyp.eq.opety%vsum)then
cycle
else
if(ktyp.eq.opekty%link)then
cycle
end if
end if
aoff=stib(tfo(0)+i1)
if(atyp.eq.opety%iprop)then
ii=0
do j=rhop1,n
do jj=rdeg(j)+1,sdeg(j),2
jk=pmap(j,jj)
do ij=1,narg
ik=stib(aoff+ij)
if(ik.eq.jk)then
ii=ii+1
else if(stib(link(0)+ik).eq.jk)then
ii=ii+1
end if
end do
end do
do jj=sdeg(j)+1,vdeg(j)
jk=pmap(j,jj)
do ij=1,narg
ik=stib(aoff+ij)
if(ik.eq.jk)then
ii=ii+1
else if(stib(link(0)+ik).eq.jk)then
ii=ii+1
end if
end do
end do
end do
else if(atyp.eq.opety%chord)then
ii=0
do j=rhop1,n
do jj=rdeg(j)+1,sdeg(j),2
if(flow(amap(j,jj),0).lt.0)then
jk=pmap(j,jj)
do ij=1,narg
ik=stib(aoff+ij)
if(ik.eq.jk)then
ii=ii+1
else if(stib(link(0)+ik).eq.jk)then
ii=ii+1
end if
end do
end if
end do
do jj=sdeg(j)+1,vdeg(j)
if(flow(amap(j,jj),0).lt.0)then
jk=pmap(j,jj)
do ij=1,narg
ik=stib(aoff+ij)
if(ik.eq.jk)then
ii=ii+1
else if(stib(link(0)+ik).eq.jk)then
ii=ii+1
end if
end do
end if
end do
end do
else if(atyp.eq.opety%psum)then
ii=0
jj=stib(aoff+1)
do j=rhop1,n
do k=rdeg(j)+1,sdeg(j),2
kk=pmap(j,k)
ik=stib(stib(pmkvfpp(0)+kk)+jj)
ij=qstoz(stcb,ik,ik-1+stib(stib(pmkvflp(0)+kk)+jj),inty%s)
Q_ERRT
ii=ii+ij
end do
do k=sdeg(j)+1,vdeg(j)
kk=pmap(j,k)
ik=stib(stib(pmkvfpp(0)+kk)+jj)
ij=qstoz(stcb,ik,ik-1+stib(stib(pmkvflp(0)+kk)+jj),inty%s)
Q_ERRT
ii=ii+ij
end do
end do
else if(ktyp.eq.opekty%bnb)then
if(atyp.eq.opety%bridge)then
j1=edgty%rb
j2=edgty%sb
else if(atyp.eq.opety%sbridge)then
j1=edgty%sb
j2=edgty%sb
else if(atyp.eq.opety%rbridge)then
j1=edgty%rb
j2=edgty%rb
else
qerrmsg(1:srec)='qgen_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=0
do j=rhop1,n
do jj=rdeg(j)+1,sdeg(j),2
ij=flow(amap(j,jj),0)
if((ij.eq.j1).or.&
(ij.eq.j2))then
jk=pmap(j,jj)
do ij=1,narg
ik=stib(aoff+ij)
if(ik.eq.jk)then
ii=ii+1
else if(stib(link(0)+ik).eq.jk)then
ii=ii+1
end if
end do
end if
end do
do jj=sdeg(j)+1,vdeg(j)
ij=flow(amap(j,jj),0)
if((ij.eq.j1).or.&
(ij.eq.j2))then
jk=pmap(j,jj)
do ij=1,narg
ik=stib(aoff+ij)
if(ik.eq.jk)then
ii=ii+1
else if(stib(link(0)+ik).eq.jk)then
ii=ii+1
end if
end do
end if
end do
end do
end if
j1=stib(tfa(0)+i1)
j2=stib(tfb(0)+i1)
if(styp.gt.0)then
if((ii.lt.j1).or.&
(ii.gt.j2))then
go to 58
end if
else if(styp.lt.0)then
if((ii.ge.j1).and.&
(ii.le.j2))then
go to 58
end if
end if
end do
do i1=1,dcoty%ubo
call qsdiag(i1,0)
Q_ERRT
end do
if(cflag(confi%qlist).eq.0)then
go to 505
end if
ndsym(symt%l)=1
do i=rhop1,n
j=rdeg(i)+1
420 continue
if(j.le.vdeg(i))then
ii=vmap(i,j)
aux=gam(i,ii)
k=j+aux
if(i.ne.ii)then
430 continue
if(j.lt.k)then
kk=1
aux=pmap(i,j)
440 continue
if(j+kk.lt.k)then
if(aux.eq.pmap(i,j+kk))then
kk=kk+1
ndsym(symt%l)=qbprod(ndsym(symt%l),kk)
Q_ERRT
go to 440
end if
end if
j=j+kk
go to 430
end if
else
do while(j.lt.k)
kk=1
aux=pmap(i,j)
460 continue
if(j+kk+kk.lt.k)then
if(aux.eq.pmap(i,j+kk+kk))then
kk=kk+1
ndsym(symt%l)=qbprod(ndsym(symt%l),kk)
Q_ERRT
go to 460
end if
end if
if(aux.eq.stib(link(0)+aux))then
jj=2
do ii=1,kk
ndsym(symt%l)=qbprod(ndsym(symt%l),jj)
Q_ERRT
end do
end if
j=j+kk+kk
end do
end if
go to 420
end if
end do
ndsym(symt%i)=qbprod(ndsym(symt%l),ndsym(symt%nl))
Q_ERRT
do i1=1,nli-nleg
j1=ex0(i1)
j2=ey0(i1)
k=pmap(j1,j2)
if(k.gt.stib(link(0)+k))then
ex(i1)=vmap(j1,j2)
ey(i1)=lmap(j1,j2)
else
ex(i1)=j1
ey(i1)=j2
end if
end do
do i=rhop1,n
if(vdeg(i).gt.0)then
xli(1:vdeg(i))=0
end if
do j=1,vdeg(i)
k=stib(stib(vparto(0)+stib(vfo(i)))+j)
do i3=1,vdeg(i)
if(xli(i3).eq.0)then
if(pmap(i,i3).eq.k)then
xli(i3)=1
ovm(i,j)=i3
iovm(i,i3)=j
go to 14
end if
end if
end do
qerrmsg(1:srec)='qgen_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
14 continue
end do
end do
dis=1
if(mflag(mflaty%cac).le.0)then
call qdis
Q_ERRT
end if
505 continue
qco(qcntr%d)=1
qsgnl=1
if(cflag(confi%qlist).gt.0)then
call qompac
Q_ERRT
end if
outd(:)=1
99 continue
return
end subroutine qgen
subroutine qdis
use,non_intrinsic::qbounds
use,non_intrinsic::qimodel
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::xli(qb2)
integer(kind=c_int_least32_t)::ii,ij,jj,i1,i2,j1,j2,j3,nf,nf1
nf=0
nf1=0
do i1=rhop1,n
do i2=1,vdeg(i1)
j1=ovm(i1,i2)
ii=pmap(i1,j1)
if(stib(antiq(0)+ii).ne.0)then
nf=nf+1
ij=vmap(i1,j1)
if(ij.le.nleg)then
ij=ps1(ij)
if(ij.gt.inco)then
jj=2*(inco-ij)
else
jj=1-2*ij
end if
else if(ii.lt.stib(link(0)+ii))then
jj=2*(amap(i1,j1)-nleg)-1
else if(ii.gt.stib(link(0)+ii))then
jj=2*(amap(i1,j1)-nleg)
else if(i1.lt.ij)then
jj=2*(amap(i1,j1)-nleg)-1
else if(i1.gt.ij)then
jj=2*(amap(i1,j1)-nleg)
else if(modulo(j1-rdeg(i1),2).ne.0)then
jj=2*(amap(i1,j1)-nleg)-1
else
jj=2*(amap(i1,j1)-nleg)
end if
if(ij.lt.0)then
nf1=nf1+1
end if
xli(nf)=jj
end if
end do
end do
266 continue
ii=0
do i1=1,nf
if(xli(i1).gt.ii)then
ii=xli(i1)
end if
end do
if(ii.gt.0)then
j1=0
j2=0
j3=nf
293 continue
if(xli(j3).gt.ii-2)then
j2=j1
j1=xli(j3)
if(j3.ne.nf)then
xli(j3)=xli(nf)
dis=-dis
end if
nf=nf-1
end if
if((j3.gt.1).and.&
(j2.eq.0))then
j3=j3-1
go to 293
end if
if(j1.gt.j2)then
dis=-dis
end if
go to 266
end if
do i1=1,inco
do i2=nf,1,-1
if(xli(i2).eq.1-2*i1)then
if(i2.ne.nf)then
xli(i2)=xli(nf)
dis=-dis
end if
nf=nf-1
exit
end if
end do
end do
do i1=rho(-1),inco+1,-1
do i2=nf,1,-1
if(xli(i2).eq.2*(inco-i1))then
if(i2.ne.nf)then
xli(i2)=xli(nf)
dis=-dis
end if
nf=nf-1
exit
end if
end do
end do
if(nf.ne.0)then
qerrmsg(1:srec)='qdis_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
99 continue
return
end subroutine qdis
subroutine qinit0
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qintr
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qwztos
character(kind=asciik,len=1)::char0
integer(kind=c_int_least32_t)::i1,ii,jj,kk
qerrt(:)=qerrty%ok
ios=0
do i1=1,len(blak)
blak(i1:i1)=achar(aspc)
end do
sthb1(1:1)=achar(aspc)
do i1=2,len(sthb1)
sthb1(i1:i1)=achar(aminus)
end do
do i1=1,2
sthb2(i1:i1)=achar(aspc)
end do
do i1=3,len(sthb2)
sthb2(i1:i1)=achar(aeq)
end do
jflag(jflaty%scstg)=0
if(asciik.eq.-1)then
qerrt(0)=qerrty%os
call quput(2)
Q_ERRT
end if
if(allocated(xstib))then
deallocate(xstib,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
if(allocated(ystib))then
deallocate(ystib,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
if(allocated(xstcb))then
deallocate(xstcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
if(allocated(ystcb))then
deallocate(ystcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
if(allocated(xstwb))then
deallocate(xstwb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
i1=0
diff0=max(128/storage_size(i1),1)
sibff(stibdst0)=sibuff0
do i1=stibdst0,1,-1
sibff(i1-1)=sibff(i1)/2
if(sibff(i1).le.max(sibff(i1-1),diff0))then
qerrt(0)=qerrty%q
call quput(9)
Q_ERRT
end if
end do
allocate(xstib(sibff(0)+1),stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
stibdst(1)=0
stibas(1)=sibff(0)-diff0
stib=>xstib
stibs(1)=0
nstjb=0
stjbs=stj0
stjb(1)=eoa
stjb(2:stj0-1)=nap
stjb(stj0)=eoa
nstsb=0
stsbs=sts0
stsb(1)=eoa
stsb(2:sts0-1)=nap
stsb(sts0)=eoa
char0=achar(aspc)
dcff0=max(128/storage_size(char0),1)
scbff(stcbdst0)=scbuff0
do i1=stcbdst0,1,-1
scbff(i1-1)=scbff(i1)/2
if(scbff(i1).le.max(scbff(i1-1),dcff0))then
qerrt(0)=qerrty%q
call quput(11)
Q_ERRT
end if
end do
allocate(character(len=scbff(0)+1)::xstcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
stcbdst(1)=0
stcbas(1)=scbff(0)-dcff0
stcb=>xstcb
stcbs(1)=0
stcbs(1)=1
stcb(1:1)=achar(aspc)
stmbs(1)=0
zbo%iref=46340
zbo%irefl=(zbo%iref)*(zbo%iref)
zbo%irefh=int(zbo%iref,c_int_least64_t)*int(zbo%irefl,c_int_least64_t)
zbo%iref10=(zbo%iref-9)/10
zbo%irefl10=(zbo%irefl-9)/10
zbo%irefh10=(zbo%irefh-9)/10
zbo%wiref=5
zbo%wirefl=10
zbo%wirefh=14
kk=1
zbo%spten=0
do while(kk.lt.zbo%irefl10)
zbo%spten=zbo%spten+1
kk=10*kk
end do
if(stibs(1).ne.0)then
qerrt(0)=qerrty%q
call quput(17)
Q_ERRT
end if
call qaoib(zbo%spten+1)
Q_ERRT
stib(stibs(1))=eoa
kk=1
do i1=1,zbo%spten
kk=10*kk
stib(i1)=kk
end do
ii=0
call qspak('2022192016;',ii,0,0,0)
Q_ERRT
call qspak('18172023192521221616;',ii,0,0,0)
Q_ERRT
call qspak('2525211716191718171620161616;',ii,0,0,0)
Q_ERRT
kk=2
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=inty%h+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
slhl(0)=stibs(1)-ii
slhp(0)=slhl(0)-ii
ii=max(aplus,aminus,azero,anine,aeq,aast)
jj=min(aplus,aminus,azero,anine,aeq,aast)
ii=max(ii,aspc,adq,asq,ausc)
jj=min(jj,aspc,adq,asq,ausc)
ii=max(ii,acol,acomma,ascol,adot,avbar,acirc)
jj=min(jj,acol,acomma,ascol,adot,avbar,acirc)
ii=max(ii,alsbr,arsbr,alcbr,arcbr,alpar,arpar)
jj=min(jj,alsbr,arsbr,alcbr,arcbr,alpar,arpar)
ii=max(ii,alt,agt,aslash,abslash)
jj=min(jj,alt,agt,aslash,abslash)
crs(1,1)=acol
crs(1,2)=acol
crs(1,3)=dcol
crs(1,4)=strty%p
crs(1,5)=0
crs(1,6)=1
crs(2,1)=ascol
crs(2,2)=ascol
crs(2,3)=dscol
crs(2,4)=strty%p
crs(2,5)=0
crs(2,6)=1
crs(3,1)=asq
crs(3,2)=asq
crs(3,3)=dsq
crs(3,4)=strty%p
crs(3,5)=1
crs(3,6)=1
crs(4,1)=aslash
crs(4,2)=aslash
crs(4,3)=dslash
crs(4,4)=strty%p
crs(4,5)=1
crs(4,6)=0
abo(1)=aspc
abo(2)=126
abo(3)=65
abo(4)=90
abo(5)=97
abo(6)=122
ii=max(ii,abo(3),abo(4),abo(5),abo(6))
jj=min(jj,abo(3),abo(4),abo(5),abo(6))
if((jj.lt.abo(1)).or.&
(ii.gt.abo(2)))then
qerrt(0)=qerrty%q
call quput(2)
Q_ERRT
end if
serrt=qerrty%ok
if(anine-azero.ne.9)then
serrt=qerrty%q
else if(abo(4)-abo(3).ne.25)then
serrt=qerrty%q
else if(abo(6)-abo(5).ne.25)then
serrt=qerrty%q
else if((abo(4).ge.abo(5)).and.&
(abo(6).ge.abo(3)))then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=qerrty%q
call quput(2)
Q_ERRT
end if
abo(0)=abo(3)-abo(5)
acf(0:255)=[(chty%nond,i1=0,255)]
acf(apcent)=chty%annot
acf(ahash)=chty%annot
acf(aast)=chty%annot
acf(ausc)=chty%usco
acf(azero:anine)=chty%digit
acf(abo(3):abo(4))=chty%ucase
acf(abo(5):abo(6))=chty%lcase
punct1(0)=stibs(1)+1
ii=129
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
stib(punct1(0):punct1(0)+127)=0
stib(punct1(0)+alf)=1
stib(punct1(0)+aspc)=1
stib(punct1(0)+acomma)=1
stib(punct1(0)+acol)=1
stib(punct1(0)+ascol)=1
stib(punct1(0)+avbar)=1
stib(punct1(0)+aeq)=1
stib(punct1(0)+alsbr)=2
stib(punct1(0)+arsbr)=2
stib(punct1(0)+alpar)=3
stib(punct1(0)+arpar)=3
stib(punct1(0)+alcbr)=4
stib(punct1(0)+arcbr)=4
stib(punct1(0)+acirc)=5
stib(punct1(0)+aminus)=-strty%minus
stib(punct1(0)+aplus)=-strty%plus
stib(punct1(0)+aast)=-strty%ast
call qinit
Q_ERRT
jflag(jflaty%init)=1
99 continue
return
end subroutine qinit0
#ifndef Q_API
integer(kind=c_int_least32_t) function qfcty(lcarg)
use,non_intrinsic::qfcon
use,non_intrinsic::qkeys
use,non_intrinsic::qbasic
implicit none
integer(kind=c_int_least32_t),intent(in)::lcarg
select case(lcarg)
case(argty%mc34)
qfcty=fcty%mc
case(argty%mc44)
qfcty=fcty%mc
case(argty%mc43)
qfcty=fcty%mc
case(argty%mc42)
qfcty=fcty%mc
case(argty%sc34)
qfcty=fcty%sc
case(argty%sc43)
qfcty=fcty%sc
case(argty%sc42)
qfcty=fcty%sc
case(argty%bc34)
qfcty=fcty%bc
case(argty%bc43)
qfcty=fcty%bc
case default
qfcty=-1
end select
99 continue
return
end function qfcty
integer(kind=c_int_least32_t) function qfcl(lcarg)
use,non_intrinsic::qkeys
use,non_intrinsic::qbasic
implicit none
integer(kind=c_int_least32_t),intent(in)::lcarg
select case(lcarg)
case(argty%mc34)
qfcl=4
case(argty%mc44)
qfcl=-4
case(argty%mc43)
qfcl=-3
case(argty%mc42)
qfcl=-2
case(argty%sc34)
qfcl=4
case(argty%sc43)
qfcl=-3
case(argty%sc42)
qfcl=-2
case(argty%bc34)
qfcl=4
case(argty%bc43)
qfcl=-3
case default
qfcl=0
end select
99 continue
return
end function qfcl
subroutine qlcas(nclarg)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstdpa,qstdw,qfcty,qfcl
integer(kind=c_int_least32_t),intent(in)::nclarg
integer(kind=c_int_least32_t)::btyp(0:argty%ubo),ctyp(1:argty%ubo)
integer(kind=c_int_least32_t)::i1,ii,ij,jj,jsa,j1,j2,j3,j4
btyp(:)=0
ctyp(:)=0
iamk=0
if(nclarg.gt.argty%ubo)then
qerrt(0)=qerrty%inp
call qiomsg(4,0,0,0)
else if(nclarg.le.0)then
qerrmsg(1:srec)='qlcas_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
serrt=qerrty%ok
jsa=0
do i1=1,nclarg
call get_command_argument(i1,coarg,jj,ios)
if(ios.ne.0)then
call qios
else if(jj.le.0)then
serrt=qerrty%inp
else if(jj.ge.qerrl0)then
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(4,0,0,0)
end if
ij=0
if(iachar(coarg(1:1)).eq.aminus)then
if(iachar(coarg(2:2)).eq.aminus)then
j1=2
else
j1=1
end if
jsa=jsa+1
if(jsa.gt.nclarg)then
serrt=qerrty%q
else
call qmstr0(coarg,j1,jj,poptcl(0),woptcl(0),aoptcl(0),ij)
if(ij.le.0)then
serrt=qerrty%inp
else
ij=stib(coptcl(0)+ij)
if(ij.le.0)then
serrt=qerrty%q
else if(ij.gt.argty%ubo)then
serrt=qerrty%q
else if(ctyp(ij).ne.0)then
serrt=qerrty%inp
else
if(qfcty(ij).gt.0)then
if(tofc.ne.0)then
serrt=qerrty%inp
else
tofc=qfcty(ij)
stofc=qfcl(ij)
qxmod=qmod%fcon
end if
btyp(i1)=ij
ctyp(ij)=ctyp(ij)+1
else
j3=0
if(ij.eq.argty%hash)then
j3=ahash
else if(ij.eq.argty%pcent)then
j3=apcent
else if(ij.eq.argty%bom)then
j3=-1
else if(ij.eq.argty%nobom)then
j3=-3
end if
if(j3.eq.0)then
btyp(i1)=ij
ctyp(ij)=1
else if(j3.gt.0)then
if(iamk.ne.0)then
serrt=qerrty%inp
else if(ctyp(argty%amk).ne.0)then
serrt=qerrty%inp
else if(i1.lt.nclarg-1)then
serrt=qerrty%inp
end if
iamk=j3
btyp(i1)=argty%amk
ctyp(argty%amk)=ctyp(argty%amk)+1
else
if(cflag(confi%bom).ne.0)then
serrt=qerrty%inp
else if(ctyp(argty%bom).ne.0)then
serrt=qerrty%inp
else if(ctyp(argty%nobom).ne.0)then
serrt=qerrty%inp
else if(i1.lt.nclarg-1)then
serrt=qerrty%inp
end if
cflag(confi%bom)=j3+2
btyp(i1)=ij
ctyp(ij)=ctyp(ij)+1
end if
end if
end if
end if
end if
else if(i1.gt.3)then
if(btyp(i1-1).eq.argty%subm)then
j1=qstdw(coarg,1,jj)
if(j1.eq.0)then
serrt=qerrty%inp
else if(ctyp(argty%submn).ne.0)then
serrt=qerrty%inp
else if(btyp(i1-1).ne.argty%subm)then
serrt=qerrty%inp
else
smodp(0)=stcbs(1)+1
smodq(0)=stcbs(1)+jj
call qaocb(jj+1)
stcb(smodp(0):stcbs(1))=coarg(1:jj)//achar(anull)
btyp(i1)=argty%submn
ctyp(argty%submn)=1
cflag(confi%subm)=1
end if
else
serrt=qerrty%inp
end if
else if(ctyp(argty%file).lt.2)then
j1=stcbs(1)+1
j2=j1-1+jj
j3=iachar(stcb(j1:j1))
j4=iachar(stcb(j2:j2))
if((j3.ne.asq).or.&
(j4.ne.asq))then
j4=1
call qaocb(jj+3)
else
j4=0
call qaocb(jj+1)
end if
j2=stcbs(1)-1
if(j4.ne.0)then
stcb(j1:j2+1)=achar(asq)//coarg(1:jj)//achar(asq)//achar(anull)
else
stcb(j1:j2+1)=coarg(1:jj)//achar(anull)
end if
if(tofc.eq.0)then
j3=qfty%ctyp
else if(nfiles.gt.0)then
j3=qfty%gotyp
else if(tofc.eq.fcty%mc)then
j3=qfty%mtyp
else if(tofc.eq.fcty%sc)then
j3=qfty%styp
else if(tofc.eq.fcty%bc)then
j3=qfty%ctyp
else
j3=qfty%gityp
end if
ii=0
call qsetfname(j3,j1,j2,ii)
if(ii.eq.0)then
serrt=qerrty%inp
else
btyp(i1)=argty%file
ctyp(argty%file)=nfiles
end if
if(tofc.ne.0)then
if(nfiles.eq.2)then
fild(nfiles)=1
end if
end if
else
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
exit
end if
end do
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(4,0,0,0)
end if
if(ctyp(argty%xtch).gt.0)then
cflag(confi%xchar)=-1
else if(stofc.gt.0)then
cflag(confi%xchar)=-1
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(4,0,0,0)
end if
do i1=1,nclarg
if(ctyp(argty%file).eq.0)then
if(nclarg.gt.1)then
if((ctyp(argty%help).ne.0).or.&
(ctyp(argty%vers).ne.0))then
qerrt(0)=qerrty%inp
end if
else if(tofc.ne.0)then
qerrt(0)=qerrty%inp
else if(ctyp(argty%help).ne.0)then
call qhelp
else if(ctyp(argty%vers).ne.0)then
dmsg=stcb(qvp:(qvp-1)+qvl)//achar(anull)
call qdwout(output_unit,sdrec,0)
end if
call qstop
else if(ctyp(argty%file).eq.1)then
if(i1.ne.1)then
serrt=qerrty%inp
else if(tofc.ne.0)then
qerrt(0)=qerrty%inp
end if
else if(ctyp(argty%file).eq.2)then
if(nclarg.lt.3)then
serrt=qerrty%inp
else if(tofc.le.0)then
serrt=qerrty%inp
end if
if(qfcty(btyp(i1)).gt.0)then
if(i1.ne.1)then
serrt=qerrty%inp
else if(btyp(i1+1).ne.argty%file)then
serrt=qerrty%inp
else if(btyp(i1+2).ne.argty%file)then
serrt=qerrty%inp
end if
else if(btyp(i1).eq.argty%file)then
if(i1.lt.2)then
serrt=qerrty%inp
else if(i1.gt.3)then
serrt=qerrty%inp
else if(qfcty(btyp(1)).lt.0)then
serrt=qerrty%inp
end if
else if(btyp(i1).eq.argty%subm)then
if(nclarg.lt.5)then
serrt=qerrty%inp
else if(i1.ne.4)then
serrt=qerrty%inp
else if(tofc.ne.fcty%mc)then
serrt=qerrty%inp
else if(stofc.ge.0)then
serrt=qerrty%inp
else if(btyp(i1+1).ne.argty%submn)then
serrt=qerrty%inp
end if
else if(btyp(i1).eq.argty%submn)then
if(nclarg.lt.5)then
serrt=qerrty%inp
else if(i1.ne.5)then
serrt=qerrty%inp
else if(tofc.ne.fcty%mc)then
serrt=qerrty%inp
else if(stofc.ge.0)then
serrt=qerrty%inp
else if(btyp(i1-1).ne.argty%subm)then
serrt=qerrty%inp
end if
end if
else
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
qerrt(0)=serrt
call qiomsg(4,0,0,0)
end if
end do
if(tofc.gt.0)then
cflag(confi%del)=0
end if
if(tofc.eq.fcty%mc)then
if(stofc.gt.0)then
call qmfc
call qstop
else if(stofc.lt.0)then
call qmbc
call qstop
end if
else if(tofc.eq.fcty%sc)then
call qsfc
call qstop
else if(tofc.eq.fcty%bc)then
call qbfc
call qstop
end if
99 continue
return
end subroutine qlcas
#endif
subroutine qinit
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qkeys
use,non_intrinsic::qmix
use,non_intrinsic::qproc,only:nloop
use,non_intrinsic::qsty
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
#ifdef Q_API
use,non_intrinsic::q_api
#endif
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::nisk,noptcl,nopt0,nopt1,nopt2,nopt3,nopt4,nopt5,nopt6,nopt7,nopt9
integer(kind=c_int_least32_t)::nos,nxts,ngfns,nstype,nmpre,stibr,uc
integer(kind=c_int_least32_t)::ii,ik,i1,jj,j1,kk
integer(kind=c_int_least32_t)::apak1(1:1),apak2(1:2),apak3(1:3)
integer(kind=c_int_least32_t)::llim(1:3),ulim(1:4)
#ifdef Q_API
integer(kind=c_int_least32_t)::j2,j3,j4
#endif
tofc=0
stofc=0
smodp(0:0)=nap
smodq(0:0)=nap
dflag(:)=0
jflag(:)=0
mflag(:)=0
do i1=1,confi%ubo
if(i1.ne.confi%dspl)then
cflag(i1)=0
end if
end do
if(qxmod.ne.qmod%auto)then
if(qxmod.ne.qmod%api)then
if(qxmod.ne.qmod%fcon)then
qerrmsg(1:srec)="execution mode not properly set"//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
end if
p_sep=aslash
#ifdef Q_API
qpsgnl=qisgnl%pre_init
#endif
if(qxmod.eq.qmod%auto)then
j1=0
do i1=1,sfiles0
stwbpf(i1)=j1
stwbuf(i1)=j1+swbuff1
j1=j1+swbuff1+1
end do
if(.not.allocated(xstwb))then
allocate(character(len=j1)::xstwb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
stwb=>xstwb
end if
iogp(:)=nap
qco(:)=0
ii=0
call qspak('8171826570132014161422;',ii,1,0,0)
Q_ERRT
qvp=stib(stibs(1)-1)
qvl=stib(stibs(1))
call qaoib(-2)
Q_ERRT
call qspak('847780637073766963;',ii,1,0,0)
Q_ERRT
qtfpp=stib(stibs(1)-1)
qtfpq=(qtfpp-1)+stib(stibs(1))
call qaoib(-2)
Q_ERRT
call qspak('0010101000817182657013716978698265846968007073766900776582750010101000;',ii,1,0,0)
Q_ERRT
qgfmp=stib(stibs(1)-1)
qgfmq=(qgfmp-1)+stib(stibs(1))
call qaoib(-2)
Q_ERRT
jj=zbo%wirefh+2
qcop(dcoty%nat)=stcbs(1)
call qaocb(jj)
Q_ERRT
stcb(qcop(dcoty%nat)+1:stcbs(1))=achar(anull)
qcop(dcoty%part)=stcbs(1)
call qaocb(jj)
Q_ERRT
stcb(qcop(dcoty%part)+1:stcbs(1))=achar(anull)
qcop(dcoty%loop)=stcbs(1)
call qaocb(jj)
Q_ERRT
stcb(qcop(dcoty%loop)+1:stcbs(1))=achar(anull)
qcop(dcoty%off)=stcbs(1)
call qaocb(jj)
Q_ERRT
stcb(qcop(dcoty%off)+1:stcbs(1))=achar(anull)
qcop(dcoty%offix)=stcbs(1)
call qaocb(jj)
Q_ERRT
stcb(qcop(dcoty%offix)+1:stcbs(1))=achar(anull)
qcol(dcoty%offix)=1
stcb(qcop(dcoty%offix)+1:qcop(dcoty%offix)+qcol(dcoty%offix))=achar(azero)
qcop(dcoty%maxc)=stcbs(1)
call qaocb(jj)
Q_ERRT
stcb(qcop(dcoty%maxc)+1:stcbs(1))=achar(anull)
qcol(dcoty%maxc)=2
stcb(qcop(dcoty%maxc)+1:qcop(dcoty%maxc)+qcol(dcoty%maxc))=achar(aminus)//achar(azero+1)
do i1=1,dcoty%ubo
call qsdiag(i1,-1)
Q_ERRT
end do
nloop=-1
rho(:)=0
psym(0)=nap
nfiles=0
nsfiles=0
dso=0
filp(:)=nap
filq(:)=nap
film(:)=0
filo(:)=0
filt(:)=0
filu(:)=non_unit
fila(:)=0
filb(:)=0
filc(:)=0
fild(:)=qfdty%dno
filw(:)=0
nlin34a=0
nlin34b=0
sekts1(0)=nap
sekts2(0)=nap
nxts=0
call qspak('83856677796869768326000059;',nxts,0,0,0)
Q_ERRT
call qspak('83696784798283260000;',nxts,0,0,0)
Q_ERRT
call qspak('00000008480900;',nxts,0,0,0)
Q_ERRT
call qspak('610000000008540900;',nxts,0,0,0)
Q_ERRT
call qspak('8082798065716584798283260000;',nxts,0,0,0)
Q_ERRT
call qspak('787978138082798065716584798283260000;',nxts,0,0,0)
Q_ERRT
call qspak('0000000846110900;',nxts,0,0,0)
Q_ERRT
call qspak('0000000835110900;',nxts,0,0,0)
Q_ERRT
call qspak('0000000846130900;',nxts,0,0,0)
Q_ERRT
call qspak('0000000835130900;',nxts,0,0,0)
Q_ERRT
call qspak('8669828473676983260000;',nxts,0,0,0)
Q_ERRT
call qspak('000000037679798083;',nxts,0,0,0)
Q_ERRT
call qspak('861368697182696983;',nxts,0,0,0)
Q_ERRT
call qspak('036873657182657783;',nxts,0,0,0)
Q_ERRT
call qspak('03718265807283;',nxts,0,0,0)
Q_ERRT
call qspak('838566847984657683;',nxts,0,0,0)
Q_ERRT
call qspak('8479846576000000;',nxts,0,0,0)
Q_ERRT
call qspak('777378638479846576000000;',nxts,0,0,0)
Q_ERRT
call qspak('00677978786967846968006873657182657783;',nxts,0,0,0)
Q_ERRT
call qspak('0067797878696784696800718265807283;',nxts,0,0,0)
Q_ERRT
call qspak('141414;',nxts,0,0,0)
Q_ERRT
call qspak('1414140000000800;',nxts,0,0,0)
Q_ERRT
call qspak('62;',nxts,0,0,0)
Q_ERRT
call qspak('0009;',nxts,0,0,0)
Q_ERRT
call qspak('000000000010000000;',nxts,0,0,0)
Q_ERRT
call qspak('13;',nxts,0,0,0)
Q_ERRT
call qspak('10;',nxts,0,0,0)
Q_ERRT
call qspak('00001010;',nxts,0,0,0)
Q_ERRT
call qspak('00000008870109;',nxts,0,0,0)
Q_ERRT
call qspak('12007673786900;',nxts,0,0,0)
Q_ERRT
call qspak('1200767378698300;',nxts,0,0,0)
Q_ERRT
call qspak('141414;',nxts,0,0,0)
Q_ERRT
call qspak('000000000003030303000000;',nxts,0,0,0)
Q_ERRT
call qspak('0026260000;',nxts,0,0,0)
Q_ERRT
kk=2
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nxts+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
xtstrl(0)=stibs(1)-ii
xtstrp(0)=xtstrl(0)-ii
nmpre=0
call qspak('876582787378712600;',nmpre,0,0,0)
Q_ERRT
call qspak('73788085840069828279822600;',nmpre,0,0,0)
Q_ERRT
call qspak('73788469827865760069828279822600;',nmpre,0,0,0)
Q_ERRT
call qspak('4115470069828279822600;',nmpre,0,0,0)
Q_ERRT
call qspak('8171826570262600;',nmpre,0,0,0)
Q_ERRT
kk=2
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nmpre+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
mprel(0)=stibs(1)-ii
mprep(0)=mprel(0)-ii
ngfns=0
call qspak('677978848279761370737669;',ngfns,0,0,0)
Q_ERRT
call qspak('776983836571691370737669;',ngfns,0,0,0)
Q_ERRT
call qspak('767366826582891370737669;',ngfns,0,0,0)
Q_ERRT
call qspak('77796869761370737669;',ngfns,0,0,0)
Q_ERRT
call qspak('83848976691370737669;',ngfns,0,0,0)
Q_ERRT
call qspak('73788085840070737669;',ngfns,0,0,0)
Q_ERRT
call qspak('7985848085840070737669;',ngfns,0,0,0)
Q_ERRT
call qspak('7985848085841370737669;',ngfns,0,0,0)
Q_ERRT
call qspak('120079858480858413667679677500;',ngfns,0,0,0)
Q_ERRT
call qspak('777968697613687382696784798289;',ngfns,0,0,0)
Q_ERRT
call qspak('79858480858413687382696784798289;',ngfns,0,0,0)
Q_ERRT
call qspak('838489766913687382696784798289;',ngfns,0,0,0)
Q_ERRT
kk=2
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=ngfns+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
xgfnl(0)=stibs(1)-ii
xgfnp(0)=xgfnl(0)-ii
nstype=0
call qspak('73786771;',nstype,0,0,0)
Q_ERRT
call qspak('79858471;',nstype,0,0,0)
Q_ERRT
call qspak('73788476;',nstype,0,0,0)
Q_ERRT
kk=2
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nstype+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
xstypl(0)=stibs(1)-ii
xstypp(0)=xstypl(0)-ii
llim(1:3)=[2047,8191,2047]
ulim(1:4)=[32767,134217727,131071,134217727]
if((scbuff0.lt.llim(2)).or.&
(scbuff0.gt.ulim(2)))then
qerrt(0)=qerrty%q
call quput(11)
Q_ERRT
end if
if((swbuff1.lt.llim(2)).or.&
(swbuff1.gt.ulim(3)))then
qerrt(0)=qerrty%q
call quput(12)
Q_ERRT
end if
if((sxbuff0.lt.llim(1)).or.&
(sxbuff0.gt.ulim(1)))then
qerrt(0)=qerrty%q
call quput(13)
Q_ERRT
end if
if((sibuff0.lt.llim(3)).or.&
(sibuff0.gt.ulim(4)))then
qerrt(0)=qerrty%q
call quput(9)
Q_ERRT
end if
if((sjbuff0.lt.llim(3)).or.&
(sjbuff0.gt.ulim(3)))then
qerrt(0)=qerrty%q
call quput(10)
Q_ERRT
end if
if((srec.le.sdrec).or.&
(srec.ge.srecx))then
qerrt(0)=qerrty%q
call quput(14)
Q_ERRT
end if
if((srecx.le.srec).or.&
(srecx.ge.qerrl0))then
qerrt(0)=qerrty%q
call quput(15)
Q_ERRT
end if
if((sdrec.ge.srec).or.&
(sdrec.lt.64))then
qerrt(0)=qerrty%q
call quput(16)
Q_ERRT
end if
ii=maxdeg
if(ii.lt.3)then
qerrmsg(1:srec)="parameter 'maxdeg' not properly set"//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=maxleg
if(ii.lt.3)then
qerrmsg(1:srec)="parameter 'maxleg' not properly set"//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=maxrho
if(ii.lt.3)then
qerrmsg(1:srec)="parameter 'maxrho' not properly set"//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=maxn
jj=2*max(maxleg,maxrho)-2
if(ii.lt.jj)then
qerrmsg(1:srec)="parameter 'maxn' not properly set"//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=maxli
jj=2*max(maxleg,maxrho)+maxrho-3
if(ii.lt.jj)then
qerrmsg(1:srec)="parameter 'maxli' not properly set"//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(abs(dekc%outp-dekc%sty).ne.1)then
qerrmsg(1:srec)="parameters dekc%outp and dekc%sty not properly set"//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
udirpq(:)=nap
uc=1
nos=1
noptcl=0
stibr=stibs(1)
apak1=[argty%vers]
call qspok('1386698283737978;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%help]
call qspok('1372697680;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%xtch]
call qspok('137879636988848265636772658283;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%hash]
call qspok('1372658372;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%pcent]
call qspok('1380698267697884;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%bom]
call qspok('138584702463667977;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%nobom]
call qspok('137879638584702463667977;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%subm]
call qspok('1383856677;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%mc34]
call qspok('137719847920;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%mc44]
call qspok('1369888482656784;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%mc43]
call qspok('137720847919;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%mc42]
call qspok('137720847918;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%sc34]
call qspok('138319847920;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%sc43]
call qspok('138320847919;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%sc42]
call qspok('138320847918;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%bc34]
call qspok('136619847920;',apak1,1,noptcl,uc,nos)
Q_ERRT
apak1=[argty%bc43]
call qspok('136620847919;',apak1,1,noptcl,uc,nos)
Q_ERRT
kk=3
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=noptcl+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
poptcl(0)=stibr
woptcl(0)=poptcl(0)+ii
aoptcl(0)=woptcl(0)+ii
coptcl(0)=aoptcl(0)+ii
jj=stibs(1)
call qsquiiz(aoptcl(0),jj,ii,kk-2,ik)
Q_ERRT
uc=0
nos=0
nopt9=0
stibr=stibs(1)
apak1=[procty%inf]
call qspok('656683;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%inf]
call qspok('6763706380797378846982;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%inf]
call qspok('67797777657868636582718577697884636779857884;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%inf]
call qspok('776588;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%inf]
call qspok('777378;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%inf]
call qspok('777968857679;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%inf]
call qspok('836976696784696863677265826375737868;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%unk]
call qspok('8170807982846576;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('816680827968;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('8173768368;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('817685808489;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('8183737190;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('818384687078;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('818384688065;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('8183846881;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('8183846883;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('8183846887;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('8183846890;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('818384897573;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('8183847990;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('81856883848975;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ninf]
call qspok('818790847983;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ins]
call qspok('68658469636578686384737769;',apak1,1,nopt9,uc,nos)
Q_ERRT
apak1=[procty%ins]
call qspok('7169846367797777657868636582718577697884;',apak1,1,nopt9,uc,nos)
Q_ERRT
kk=3
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt9+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt9(0)=stibr
wopt9(0)=popt9(0)+ii
aopt9(0)=wopt9(0)+ii
copt9(0)=aopt9(0)+ii
jj=stibs(1)
call qsquiiz(aopt9(0),jj,ii,kk-2,ik)
Q_ERRT
uc=1
nos=0
nisk=0
stibr=stibs(1)
apak3=[dekc%conf,dekc%psep,stmty%uopt]
call qspok('677978707371;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%psep,dekc%odir,stmty%uopt]
call qspok('836980658265847982;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%odir,dekc%sdir,stmty%uopt]
call qspok('79858480858463687382;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%sdir,dekc%mdir,stmty%uopt]
call qspok('838489766963687382;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%mdir,dekc%ldir,stmty%uopt]
call qspok('777968697663687382;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%ldir,dekc%odir,stmty%uopt]
call qspok('76736663687382;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%msg,dekc%sty,stmty%uopt]
call qspok('7769838365716983;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%sty,dekc%outp,stmty%dopt]
call qspok('8384897669;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%outp,dekc%sty,stmty%dopt]
call qspok('798584808584;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%lib,dekc%model,stmty%uopt]
call qspok('767366;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%model,dekc%in,stmty%ureq]
call qspok('7779686976;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%in,dekc%out,stmty%ureq]
call qspok('7378;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%out,dekc%loop,stmty%ureq]
call qspok('798584;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%loop,dekc%loopk,stmty%ureq]
call qspok('7679798083;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%loopk,dekc%opt,stmty%uopt]
call qspok('76797980637779776978848577;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%opt,dekc%part,stmty%uopt]
call qspok('79808473797883;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%part,dekc%off,stmty%uopt]
call qspok('806582847384737978;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%off,dekc%maxc,stmty%uopt]
call qspok('737868698863797070836984;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%maxc,dekc%zerok,stmty%uopt]
call qspok('6779857884638479;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%zerok,dekc%loopk,stmty%uopt]
call qspok('90698279637779776978848577;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%tru,dekc%fal,stmty%dopt]
call qspok('84828569;',apak3,3,nisk,uc,nos)
Q_ERRT
apak3=[dekc%fal,dekc%tru,stmty%dopt]
call qspok('7065768369;',apak3,3,nisk,uc,nos)
Q_ERRT
kk=5
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nisk+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
pisk(0)=stibr
wisk(0)=pisk(0)+ii
aisk(0)=wisk(0)+ii
cisk(0)=aisk(0)+ii
jj=stibs(1)
call qsquiiz(aisk(0),jj,ii,kk-2,ik)
Q_ERRT
fisk(0)=cisk(0)+ik
oisk(0)=fisk(0)+ik
uc=1
nos=0
nopt0=0
stibr=stibs(1)
#ifndef Q_API
apak2=[confi%qlist,-1]
call qspok('787976738384;',apak2,2,nopt0,uc,nos)
apak2=[confi%dspl,dsplmod%noinfo]
call qspok('787973787079;',apak2,2,nopt0,uc,nos)
apak2=[confi%dspl,dsplmod%info]
call qspok('73787079;',apak2,2,nopt0,uc,nos)
apak2=[confi%dspl,dsplmod%vrbs]
call qspok('86698266798369;',apak2,2,nopt0,uc,nos)
apak2=[confi%lf,-1]
call qspok('7670;',apak2,2,nopt0,uc,nos)
#endif
apak2=[confi%dspl,dsplmod%dbg]
call qspok('6869668571;',apak2,2,nopt0,uc,nos)
Q_ERRT
apak2=[confi%flsh,1]
call qspok('7076858372;',apak2,2,nopt0,uc,nos)
Q_ERRT
apak2=[confi%del,1]
call qspok('686976698469;',apak2,2,nopt0,uc,nos)
Q_ERRT
apak2=[confi%noblank,1]
call qspok('7879667665787583;',apak2,2,nopt0,uc,nos)
Q_ERRT
apak2=[confi%nontnls,1]
call qspok('7879637884787683;',apak2,2,nopt0,uc,nos)
Q_ERRT
apak2=[confi%bom,1]
call qspok('8584702463667977;',apak2,2,nopt0,uc,nos)
Q_ERRT
apak2=[confi%bom,-1]
call qspok('7879638584702463667977;',apak2,2,nopt0,uc,nos)
Q_ERRT
kk=4
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt0+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt0(0)=stibr
wopt0(0)=popt0(0)+ii
aopt0(0)=wopt0(0)+ii
copt0(0)=aopt0(0)+ii
jj=stibs(1)
call qsquiiz(aopt0(0),jj,ii,kk-2,ik)
Q_ERRT
xopt0(0)=copt0(0)+ik
uc=1
nos=1
nopt1=0
stibr=stibs(1)
apak2=[dflaty%nob,1]
call qspok('787966827368716983;',apak2,2,nopt1,uc,nos)
Q_ERRT
call qspok('7978698073;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nob,-1]
call qspok('66827368716983;',apak2,2,nopt1,uc,nos)
Q_ERRT
call qspok('7978698082;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%norb,1]
call qspok('78798266827368716983;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%norb,-1]
call qspok('8266827368716983;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nosb,1]
call qspok('78798366827368716983;',apak2,2,nopt1,uc,nos)
Q_ERRT
call qspok('78798465688079766983;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nosb,-1]
call qspok('8366827368716983;',apak2,2,nopt1,uc,nos)
Q_ERRT
call qspok('8465688079766983;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%edge,-1]
call qspok('78796968716983;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%edge,1]
call qspok('6968716983;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%onsh,1]
call qspok('79788372697676;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%onsh,-1]
call qspok('7970708372697676;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%onshx,1]
call qspok('7978837269767688;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%onshx,-1]
call qspok('797070837269767688;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nosig,1]
call qspok('7879837371776583;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nosig,-1]
call qspok('837371776583;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nosn,1]
call qspok('7879837865737683;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nosn,-1]
call qspok('837865737683;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%cyc,1]
call qspok('6789677673;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%cyc,-1]
call qspok('6789677682;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%ovi,1]
call qspok('7978698673;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%ovi,-1]
call qspok('7978698682;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%bip,1]
call qspok('667380658284;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%bip,-1]
call qspok('787978667380658284;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nosl,1]
call qspok('7879836976707679798083;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nosl,-1]
call qspok('836976707679798083;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nodl,1]
call qspok('787968737679798083;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nodl,-1]
call qspok('68737679798083;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nopa,1]
call qspok('78798065826576766976;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%nopa,-1]
call qspok('8065826576766976;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%simp,1]
call qspok('837377807669;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%simp,-1]
call qspok('787984837377807669;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%topo,1]
call qspok('8479807976;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%newe,1]
call qspok('78698763697673787583;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%newt,1]
call qspok('786987638479807976797189;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%newp,1]
call qspok('78698763806582847384737978;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%newc,1]
call qspok('786987637679798083;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%idx,1]
call qspok('736863698884;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%fl,1]
call qspok('707679798083;',apak2,2,nopt1,uc,nos)
Q_ERRT
apak2=[dflaty%fl,-1]
call qspok('787984707679798083;',apak2,2,nopt1,uc,nos)
Q_ERRT
kk=4
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt1+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt1(0)=stibr
wopt1(0)=popt1(0)+ii
aopt1(0)=wopt1(0)+ii
copt1(0)=aopt1(0)+ii
jj=stibs(1)
call qsquiiz(aopt1(0),jj,ii,kk-2,ik)
Q_ERRT
xopt1(0)=copt1(0)+ik
uc=1
nos=0
nopt2=0
stibr=stibs(1)
apak2=[opety%iprop,opekty%bnb]
call qspok('7380827980;',apak2,2,nopt2,uc,nos)
Q_ERRT
apak2=[opety%bridge,opekty%bnb]
call qspok('668273687169;',apak2,2,nopt2,uc,nos)
Q_ERRT
apak2=[opety%sbridge,opekty%bnb]
call qspok('83668273687169;',apak2,2,nopt2,uc,nos)
Q_ERRT
apak2=[opety%rbridge,opekty%bnb]
call qspok('82668273687169;',apak2,2,nopt2,uc,nos)
Q_ERRT
apak2=[opety%chord,opekty%bnb]
call qspok('6772798268;',apak2,2,nopt2,uc,nos)
Q_ERRT
apak2=[opety%vsum,opekty%sum]
call qspok('86838577;',apak2,2,nopt2,uc,nos)
Q_ERRT
apak2=[opety%psum,opekty%sum]
call qspok('80838577;',apak2,2,nopt2,uc,nos)
Q_ERRT
apak2=[opety%elink,opekty%link]
call qspok('6976737875;',apak2,2,nopt2,uc,nos)
Q_ERRT
apak2=[opety%plink,opekty%link]
call qspok('8076737875;',apak2,2,nopt2,uc,nos)
Q_ERRT
kk=4
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt2+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt2(0)=stibr
wopt2(0)=popt2(0)+ii
aopt2(0)=wopt2(0)+ii
copt2(0)=aopt2(0)+ii
jj=stibs(1)
call qsquiiz(aopt2(0),jj,ii,kk-2,ik)
Q_ERRT
xopt2(0)=copt2(0)+ik
mcopt2=0
ncopt2=0
do i1=1,ik-1
j1=stib(copt2(0)+i1)
if((j1.eq.0).or.&
(j1.lt.mcopt2))then
qerrmsg(1:srec)='qinit_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
else
if(j1.gt.mcopt2)then
ncopt2=ncopt2+1
end if
mcopt2=j1
end if
end do
uc=1
nos=0
nopt3=0
stibr=stibs(1)
apak1=[elinty%incl]
call qspok('73786776;',apak1,1,nopt3,uc,nos)
Q_ERRT
apak1=[elinty%excl]
call qspok('69886776;',apak1,1,nopt3,uc,nos)
Q_ERRT
kk=3
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt3+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt3(0)=stibr
wopt3(0)=popt3(0)+ii
aopt3(0)=wopt3(0)+ii
copt3(0)=aopt3(0)+ii
jj=stibs(1)
call qsquiiz(aopt3(0),jj,ii,kk-2,ik)
Q_ERRT
uc=1
nos=0
nopt4=0
stibr=stibs(1)
call qspak('8479,1;',nopt4,0,uc,nos)
Q_ERRT
call qspak('84728285,1;',nopt4,0,uc,nos)
Q_ERRT
call qspak('84728279857172,1;',nopt4,0,uc,nos)
Q_ERRT
kk=3
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt4+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt4(0)=stibr
wopt4(0)=popt4(0)+ii
aopt4(0)=wopt4(0)+ii
copt4(0)=aopt4(0)+ii
jj=stibs(1)
call qsquiiz(aopt4(0),jj,ii,kk-2,ik)
Q_ERRT
pot(0)=1
do i1=1,maxpot
pot(i1)=2*pot(i1-1)
end do
uc=0
nos=0
call qspak('6885657613;',ii,1,uc,nos)
Q_ERRT
dprefp=stib(stibs(1)-1)
dprefl=stib(stibs(1))
call qaoib(-2)
Q_ERRT
uc=0
nos=0
nske=0
stibr=stibs(1)
call qspak('8082797679718569,1,0,0,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('68736571826577,2,0,0,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('6980737679718569,3,0,0,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('69887384,4,0,0,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('8384658469776978846376797980,11,1,5,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('838465846977697884638385666376797980,12,1,5,1,0;',nske,0,uc,nos)
Q_ERRT
call qspak('73786376797980,13,1,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('736376797980,13,1,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7985846376797980,14,1,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('796376797980,14,1,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('808279806571658479826376797980,15,1,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('806376797980,15,1,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('8669828469886376797980,16,1,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('866376797980,16,1,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('8265896376797980,17,1,2,8,0;',nske,0,uc,nos)
Q_ERRT
call qspak('826376797980,17,1,2,8,0;',nske,0,uc,nos)
Q_ERRT
call qspak('77797769788485776376797980,18,1,2,20,0;',nske,0,uc,nos)
Q_ERRT
call qspak('776376797980,18,1,2,20,0;',nske,0,uc,nos)
Q_ERRT
call qspak('697868,19,1,7,63,0;',nske,0,uc,nos)
Q_ERRT
call qspak('66656775,22,2,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('78698776737869,29,5,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7073697668,31,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('70,31,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('70736976686383737178,32,4,7,23,0;',nske,0,uc,0)
Q_ERRT
call qspak('706383737178,32,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('68856576137073697668,33,4,7,23,0;',nske,0,uc,0)
Q_ERRT
call qspak('688565761370,33,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7073697668638384898069,34,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7779776978848577,35,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('77797769788485776384698277,36,4,2,32,0;',nske,0,uc,nos)
Q_ERRT
call qspak('68856576137779776978848577,37,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('688565761377797769788485776384698277,38,4,2,32,0;',nske,0,uc,nos)
Q_ERRT
call qspak('70736976686384898069,40,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('706384898069,40,4,7,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('80827980657165847982637378686988,41,4,2,52,0;',nske,0,uc,nos)
Q_ERRT
call qspak('80637378686988,41,4,2,52,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7073697668637378686988,42,4,7,55,0;',nske,0,uc,nos)
Q_ERRT
call qspak('70637378686988,42,4,7,55,0;',nske,0,uc,nos)
Q_ERRT
call qspak('826589637378686988,43,4,2,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('82637378686988,43,4,2,23,0;',nske,0,uc,nos)
Q_ERRT
call qspak('866982846988637378686988,44,4,2,31,0;',nske,0,uc,nos)
Q_ERRT
call qspak('86637378686988,44,4,2,31,0;',nske,0,uc,nos)
Q_ERRT
call qspak('68856576137073697668637378686988,45,4,2,52,0;',nske,0,uc,nos)
Q_ERRT
call qspak('688565761370637378686988,45,4,2,52,0;',nske,0,uc,nos)
Q_ERRT
call qspak('6885657613826589637378686988,46,4,2,20,0;',nske,0,uc,0)
Q_ERRT
call qspak('688565761382637378686988,46,4,2,20,0;',nske,0,uc,nos)
Q_ERRT
call qspak('6885657613866982846988637378686988,47,4,2,20,0;',nske,0,uc,nos)
Q_ERRT
call qspak('688565761386637378686988,47,4,2,20,0;',nske,0,uc,nos)
Q_ERRT
call qspak('86698284698863686971826969,48,4,2,31,0;',nske,0,uc,nos)
Q_ERRT
call qspak('8663686971826969,48,4,2,31,0;',nske,0,uc,nos)
Q_ERRT
call qspak('688565761386698284698863686971826969,49,4,2,20,0;',nske,0,uc,nos)
Q_ERRT
call qspak('68856576138663686971826969,49,4,2,20,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7378637378686988,52,4,7,1,0;',nske,0,uc,nos)
Q_ERRT
call qspak('73637378686988,52,4,7,1,0;',nske,0,uc,nos)
Q_ERRT
call qspak('798584637378686988,53,4,7,2,0;',nske,0,uc,nos)
Q_ERRT
call qspak('79637378686988,53,4,7,2,0;',nske,0,uc,nos)
Q_ERRT
call qspak('766971637378686988,54,4,7,3,0;',nske,0,uc,nos)
Q_ERRT
call qspak('707369766863838566,55,4,7,55,0;',nske,0,uc,nos)
Q_ERRT
call qspak('6885657613707369766863838566,57,4,2,52,0;',nske,0,uc,nos)
Q_ERRT
call qspak('83737178,61,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7773788583,62,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('78698763697673787583,63,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('786987638479807976797189,64,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('78698763806582847384737978,65,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('786987637679798083,66,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('767979808317,67,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('767979808318,68,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7679798083,69,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('838977776984828963706567847982,70,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('838977776984828963788577666982,71,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('787978767967657663838977776984828963788577666982,72,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('767967657663838977776984828963788577666982,73,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('8082798065716584798283,74,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('8669828473676983,76,3,2,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('76697183,77,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('76697183637378,78,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('7669718363798584,79,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('68736571826577637378686988,80,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('687365718265776367798578846982,81,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('737868698863797070836984,82,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('708576766384737769,83,3,5,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('80827971826577,84,3,5,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('8265876384737769,85,3,5,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('76797980637779776978848577,86,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('90698279637779776978848577,87,3,7,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('83856663838465846977697884,90,4,5,2,0;',nske,0,uc,nos)
Q_ERRT
#ifndef Q_API
call qspak('81707376696377658275,91,3,1,0,0;',nske,0,uc,nos)
#endif
call qspak('677977776578686368658465,100,4,5,3,0;',nske,0,uc,nos)
Q_ERRT
call qspak('677977776578686376797980,101,1,5,0,0;',nske,0,uc,nos)
Q_ERRT
call qspak('6779777765786863767378696376797980,102,1,5,1,0;',nske,0,uc,nos)
Q_ERRT
kk=7
if(stibs(1)-stibr.ne.kk*nske)then
qerrmsg(1:srec)='qinit_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nske+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
pske(0)=stibr
wske(0)=pske(0)+ii
aske(0)=wske(0)+ii
kc(0)=aske(0)+ii
jj=stibs(1)
call qsquiiz(aske(0),jj,ii,kk-2,ik)
Q_ERRT
kla(0)=kc(0)+ik
kse(0)=kla(0)+ik
klo(0)=kse(0)+ik
sef(0)=klo(0)+ik
if(size(skep).lt.stib(kc(0)+ik-1))then
qerrmsg(1:srec)="parameter skep0 not properly set"//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
skep(:)=0
nopt5=0
uc=1
nos=1
stibr=stibs(1)
apak2=[dekm%sbm_stm,0]
call qspok('838566777968697683;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%sk_stm,mllty%mpf]
call qspok('806383696784798283;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%sk_stm,mllty%mvf]
call qspok('866383696784798283;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%c_stm,mllty%mc]
call qspok('677978838465788483;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%f_stm,mllty%mff]
call qspok('7063708578678473797883;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%f_stm,mllty%mpf]
call qspok('8063708578678473797883;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%f_stm,mllty%mvf]
call qspok('8663708578678473797883;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%sbmb_stm,0]
call qspok('8385667779686976;',apak2,2,nopt5,uc,0)
Q_ERRT
apak2=[dekm%sbmb_sk,0]
call qspok('7378677685686983;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%sbmb_sk,1]
call qspok('6988677685686983;',apak2,2,nopt5,uc,nos)
Q_ERRT
apak2=[dekm%sbmb_end,0]
call qspok('697868;',apak2,2,nopt5,uc,0)
Q_ERRT
apak2=[dekm%skb_stm,0]
call qspok('836967847982;',apak2,2,nopt5,uc,0)
Q_ERRT
kk=4
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt5+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt5(0)=stibr
wopt5(0)=popt5(0)+ii
aopt5(0)=wopt5(0)+ii
copt5(0)=aopt5(0)+ii
jj=stibs(1)
call qsquiiz(aopt5(0),jj,ii,kk-2,ik)
Q_ERRT
xopt5(0)=copt5(0)+ik
nopt7=0
uc=1
nos=0
stibr=stibs(1)
apak1=[strty%z]
call qspok('73788469716982;',apak1,1,nopt7,uc,nos)
Q_ERRT
kk=3
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt7+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt7(0)=stibr
wopt7(0)=popt7(0)+ii
aopt7(0)=wopt7(0)+ii
copt7(0)=aopt7(0)+ii
jj=stibs(1)
call qsquiiz(aopt7(0),jj,ii,kk-2,ik)
Q_ERRT
nopt6=0
nos=1
uc=1
stibr=stibs(1)
apak1=[phity%notdp]
call qspok('78798465688079766983;',apak1,1,nopt6,uc,nos)
Q_ERRT
apak1=[phity%ext]
call qspok('6988846982786576;',apak1,1,nopt6,uc,nos)
Q_ERRT
apak1=[phity%int]
call qspok('7378846982786576;',apak1,1,nopt6,uc,nos)
Q_ERRT
kk=3
call qaoib(kk)
Q_ERRT
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nopt6+1
call qtrm(kk,ii,stibs(1))
Q_ERRT
popt6(0)=stibr
wopt6(0)=popt6(0)+ii
aopt6(0)=wopt6(0)+ii
copt6(0)=aopt6(0)+ii
jj=stibs(1)
call qsquiiz(aopt6(0),jj,ii,kk-2,ik)
Q_ERRT
nphi=0
nprop=0
npprop=0
nvert=0
nblok=0
nblokfp=0
nudk=0
ngmk=0
npmk=0
nvmk=0
aaf(0)=6
aaf(1)=6
aaf(2)=6
aaf(3)=5
aaf(4)=5
csyfty(:)=0
csyfty(qfty%ctyp)=5
csyfty(qfty%mtyp)=6
#ifndef Q_API
if(qxmod.ne.qmod%api)then
ii=int(command_argument_count(),c_int_least32_t)
if(ii.gt.0)then
if(ii.gt.argty%ubo)then
qerrt(0)=qerrty%inp
call qiomsg(4,0,0,0)
else
call qlcas(ii)
end if
end if
end if
#endif
#ifdef Q_API
if(qxmod.eq.qmod%api)then
j4=0
if(associated(stwb))then
do i1=1,srec
jj=iachar(coarg(i1:i1))
if(jj.eq.anull)then
j4=i1-1
exit
end if
end do
end if
if(j4.gt.0)then
j1=stcbs(1)+1
j3=srec
do i1=1,j4
jj=iachar(coarg(i1:i1))
if(jj.ne.aspc)then
j3=i1
exit
end if
end do
if(j3.le.j4)then
ii=j4-(j3-1)
if((iachar(coarg(j3:j3)).eq.asq).and.&
(iachar(coarg(j4:j4)).eq.asq))then
ii=ii-2
j3=j3+1
j4=j4-1
end if
if(ii.gt.0)then
call qaocb(ii+3)
Q_ERRT
stcb(j1:stcbs(1))=achar(asq)//coarg(j3:j4)//achar(asq)//achar(anull)
else
j4=-1
end if
end if
end if
ii=0
if(j4.gt.0)then
j2=stcbs(1)-1
call qsetfname(qfty%ctyp,j1,j2,ii)
Q_ERRT
end if
if(ii.le.0)then
qerrt(0)=qerrty%inp
call qpomsg(5)
Q_ERRT
end if
end if
#endif
if(nfiles.eq.0)then
if(qxmod.eq.qmod%auto)then
qerrt(0)=qerrty%inp
call qcfmsg(1,0,0)
Q_ERRT
end if
end if
qobsol(:)=0
99 continue
return
end subroutine qinit
subroutine qsquiiz(ia,ib,jj,kk,uu)
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ia,ib,jj,kk
integer(kind=c_int_least32_t),intent(out)::uu
integer(kind=c_int_least32_t)::i1,i2,i3,ii,j1,xp1,xp2,xp3
if((ia.le.0).or.&
(ia.ge.ib))then
go to 80
else if((jj.le.1).or.&
(kk.le.0))then
go to 80
else if(ib-ia.ne.jj*kk)then
go to 80
end if
ii=ia-jj
do i1=0,kk
ii=ii+jj
if(stib(ii).ne.eoa)then
go to 80
end if
end do
xp1=stibs(1)
call qaoib(jj)
Q_ERRT
stib(xp1+1:stibs(1)-1)=0
stib(stibs(1))=eoa
i3=1
stib(xp1+1)=1
xp2=ia+1
do i1=2,jj-1
xp2=xp2+1
j1=xp2-jj
do i2=1,kk
j1=j1+jj
if(stib(j1).ne.stib(j1-1))then
i3=i3+1
stib(xp1+i1)=1
exit
end if
end do
end do
ii=i3+1
call qaoib(ii*kk)
Q_ERRT
xp2=stibs(1)
do i1=kk-1,0,-1
stib(xp2)=eoa
xp2=xp2-ii
end do
uu=0
do i1=1,jj-1
if(stib(xp1+i1).ne.0)then
uu=uu+1
xp2=ia+i1-jj
xp3=xp1+jj+uu-ii
do i2=1,kk
xp2=xp2+jj
xp3=xp3+ii
stib(xp3)=stib(xp2)
end do
end if
stib(xp1+i1)=uu
end do
uu=uu+1
ii=xp1-ia
if(ii.gt.0)then
call qxipht(xp1+1,stibs(1),-ii)
Q_ERRT
call qaoib(-ii)
Q_ERRT
else
go to 80
end if
go to 99
80 continue
qerrmsg(1:srec)='qsquiiz_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
99 continue
return
end subroutine qsquiiz
subroutine qmfmsg(jj,k3,k4)
use,non_intrinsic::qfiles
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj,k3,k4
integer(kind=c_int_least32_t)::i1,k1,k2,ifile
ifile=0
if((0.le.k3).and.(k3.le.k4))then
i1=0
do i1=1,nfiles
if(filt(i1).eq.qfty%mtyp)then
ifile=i1
exit
end if
end do
end if
select case(jj)
case(1)
qerrmsg(1:srec)="statement too long,"//achar(anull)
case(2)
qerrmsg(1:srec)="wrong syntax or unexpected statement,"//achar(anull)
case(3)
qerrmsg(1:srec)="one or more propagators consist of non-interacting field(s)"//achar(anull)
ifile=0
case(4)
qerrmsg(1:srec)="unknown field in"//achar(anull)
case(5)
qerrmsg(1:srec)="field appears in more than one propagator"//achar(anull)
ifile=0
case(6)
qerrmsg(1:srec)="input (sub)model contains no propagator statements"//achar(anull)
ifile=0
case(7)
qerrmsg(1:srec)="input (sub)model contains no vertex statements"//achar(anull)
ifile=0
case(8)
qerrmsg(1:srec)="at least one field is not in any vertex"//achar(anull)
case(9)
qerrmsg(1:srec)="vertex degree is too small,"//achar(anull)
case(10)
qerrmsg(1:srec)="vertex degree is too large,"//achar(anull)
case(11)
qerrmsg(1:srec)="odd vertex in"//achar(anull)
case(12)
qerrmsg(1:srec)="duplicate function or constant,"//achar(anull)
case(13)
qerrmsg(1:srec)="wrong dimension for function(s),"//achar(anull)
case(14)
qerrmsg(1:srec)="both constants and functions have to be declared in the"//achar(anull)
case(15)
qerrmsg(1:srec)="unknown function or constant,"//achar(anull)
case(16)
qerrmsg(1:srec)="no image defined for function,"//achar(anull)
case(17)
qerrmsg(1:srec)="wrong-type value for constant or function,"//achar(anull)
case(18)
qerrmsg(1:srec)="unknown or undefined sector,"//achar(anull)
case(19)
qerrmsg(1:srec)="empty or incomplete sector block,"//achar(anull)
case(20)
qerrmsg(1:srec)="duplicate sector,"//achar(anull)
case(21)
qerrmsg(1:srec)="unreferenced sector,"//achar(anull)
case(22)
qerrmsg(1:srec)="identifier is already defined,"//achar(anull)
case(23)
qerrmsg(1:srec)="duplicate submodel,"//achar(anull)
case(24)
qerrmsg(1:srec)="empty or incomplete submodel definition"//achar(anull)
ifile=0
case(25)
qerrmsg(1:srec)="unknown or undefined submodel(s),"//achar(anull)
case(26)
qerrmsg(1:srec)="undefined constant detected,"//achar(anull)
case(27)
qerrmsg(1:srec)="no actual propagators, all fields tagged 'external'"//achar(anull)
case(28)
qerrmsg(1:srec)="input model has duplicate vertices"//achar(anull)
ifile=0
case(29)
qerrmsg(1:srec)="too many vertices defined"//achar(anull)
ifile=0
case(30)
qerrmsg(1:srec)="too many fields defined"//achar(anull)
ifile=0
case(31)
qerrmsg(1:srec)="input model can be split into disjoint sub-models"//achar(anull)
ifile=0
case default
qerrt(0)=qerrty%q
qerrmsg(1:srec)="qmfmsg_1"//achar(anull)
end select
k1=k3
k2=k4
call qmput(k1,k2,ifile)
Q_ERRT
99 continue
return
end subroutine qmfmsg
subroutine qcfmsg(jj,k3,k4)
use,non_intrinsic::qfiles
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj,k3,k4
integer(kind=c_int_least32_t)::k1,k2,ifile
ifile=0
if((k3.ge.0).and.(k3.le.k4))then
do while(ifile.lt.nfiles)
ifile=ifile+1
if(filt(ifile).eq.qfty%ctyp)then
exit
end if
end do
end if
select case(jj)
case(1)
qerrmsg(1:srec)="control-file is not defined"//achar(anull)
ifile=0
case(2)
qerrmsg(1:srec)="check 'config' statement"//achar(anull)
ifile=0
case(4)
qerrmsg(1:srec)="invalid path separator,"//achar(anull)
case(5)
qerrmsg(1:srec)="'output_dir' is not defined"//achar(anull)
ifile=0
case(6)
qerrmsg(1:srec)="identical default directories"//achar(anull)
ifile=0
case(7)
qerrmsg(1:srec)="default directory name does not end with a path separator"//achar(anull)
ifile=0
case(8)
qerrmsg(1:srec)="wrong 'style'/'output' statement pairing"//achar(anull)
ifile=0
case(9)
qerrmsg(1:srec)="too many 'style' and/or 'output' statements"//achar(anull)
ifile=0
case(11)
qerrmsg(1:srec)="all input/output files should be distinct"//achar(anull)
ifile=0
case(12)
qerrmsg(1:srec)="input submodel not found or not specified"//achar(anull)
ifile=0
case(13)
qerrmsg(1:srec)="unknown external field(s)"//achar(anull)
ifile=0
case(14)
qerrmsg(1:srec)="odd number of external anticommuting fields"//achar(anull)
ifile=0
case(16)
qerrmsg(1:srec)="external field(s) cannot link-up with any vertex"//achar(anull)
ifile=0
case(17)
qerrmsg(1:srec)="external fields cannot be connected"//achar(anull)
ifile=0
case(18)
qerrmsg(1:srec)="one or more external fields have been declared 'internal'"//achar(anull)
ifile=0
case(19)
qerrmsg(1:srec)="the external momenta are not defined"//achar(anull)
ifile=0
case(21)
qerrmsg(1:srec)="no external fields"//achar(anull)
ifile=0
case(22)
qerrmsg(1:srec)="too many external fields"//achar(anull)
ifile=0
case(23)
qerrmsg(1:srec)="case loops=0, #legs=2 not accepted"//achar(anull)
ifile=0
case(24)
qerrmsg(1:srec)="check #legs, loops"//achar(anull)
ifile=0
case(26)
qerrmsg(1:srec)="check 'loops' statement"//achar(anull)
ifile=0
case(27)
qerrmsg(1:srec)="too large #legs and/or loops"//achar(anull)
ifile=0
case(28)
qerrmsg(1:srec)="'loop_momentum' statement not found"//achar(anull)
ifile=0
case(29)
qerrmsg(1:srec)="using default <zero_momentum>"//achar(anull)
ifile=0
case(31)
qerrmsg(1:srec)="conflict between names of external/internal/zero momenta"//achar(anull)
ifile=0
case(32)
qerrmsg(1:srec)="check 'options' statement (and possibly input process)"//achar(anull)
ifile=0
case(33)
qerrmsg(1:srec)="input partition is not valid"//achar(anull)
ifile=0
case(34)
qerrmsg(1:srec)="using default <index_offset>"//achar(anull)
ifile=0
case(36)
qerrmsg(1:srec)="invalid argument(s)"//achar(anull)
case(37)
qerrmsg(1:srec)="inconsistent 'elink' statement"//achar(anull)
ifile=0
case(38)
qerrmsg(1:srec)="trivial 'elink' statement"//achar(anull)
ifile=0
case default
qerrt(0)=qerrty%q
qerrmsg(1:srec)="qcfmsg_1"//achar(anull)
end select
k1=k3
k2=k4
call qmput(k1,k2,ifile)
Q_ERRT
99 continue
return
end subroutine qcfmsg
subroutine qcfmsg0(jj,k3,k4)
use,non_intrinsic::qfiles
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj,k3,k4
integer(kind=c_int_least32_t)::k1,k2,ifile
ifile=0
if((k3.ge.0).and.(k3.le.k4))then
do while(ifile.lt.nfiles)
ifile=ifile+1
if(filt(ifile).eq.qfty%ctyp)then
exit
end if
end do
end if
select case(jj)
case(1)
qerrmsg(1:srec)="wrong syntax or unexpected statement,"//achar(anull)
case(2)
qerrmsg(1:srec)="statement too long,"//achar(anull)
case(3)
qerrmsg(1:srec)="incomplete"//achar(anull)
case default
qerrt(0)=qerrty%q
qerrmsg(1:srec)="qcfmsg0_1"//achar(anull)
end select
k1=k3
k2=k4
call qmput(k1,k2,ifile)
Q_ERRT
99 continue
return
end subroutine qcfmsg0
subroutine qstymsg(jj,k3,k4,jfile,j1,j2)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer,only:stcb
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj,jfile,k3,k4,j1,j2
integer(kind=c_int_least32_t)::i1,k1,k2,ifile
ifile=jfile
qerrt(0)=qerrty%inp
select case(jj)
case(1)
qerrmsg(1:srec)="incomplete"//achar(anull)
case(2)
qerrmsg(1:srec)="unknown non-intrinsic style-keyword,"//achar(anull)
case(3)
qerrmsg(1:srec)="M-constants cannot be prefixed with 'dual-',"//achar(anull)
case(4)
qerrmsg(1:srec)="functions cannot appear outside a loop,"//achar(anull)
case(5)
qerrmsg(1:srec)="f-functions cannot appear in the (strict) vertex loop,"//achar(anull)
case(6)
qerrmsg(1:srec)="p-functions cannot appear in the (strict) vertex loop,"//achar(anull)
case(7)
qerrmsg(1:srec)="p-functions cannot be prefixed with 'dual-'"//achar(anull)
case(8)
qerrmsg(1:srec)="v-functions cannot be prefixed with 'dual-' except in the propagator_loop"//achar(anull)
case(9)
qerrmsg(1:srec)="too many nested loops,"//achar(anull)
case(10)
qerrmsg(1:srec)="runtime error while processing <prologue>"//achar(anull)
case(11)
qerrmsg(1:srec)="runtime error while processing <diagram>"//achar(anull)
case(12)
qerrmsg(1:srec)="runtime error while processing <epilogue>"//achar(anull)
case(13)
qerrmsg(1:srec)="some style-keyword(s) cannot be translated"//achar(anull)
case(14)
qerrmsg(1:srec)="some style-keyword(s) are too long"//achar(anull)
case default
qerrt(0)=qerrty%q
qerrmsg(1:srec)="qstymsg_1"//achar(anull)
end select
if(0.lt.j1)then
if(j1.le.j2)then
k1=j2-(j1-1)
if(k1.lt.sdrec)then
k2=0
do i1=1,len(qerrmsg)
if(iachar(qerrmsg(i1:i1)).eq.anull)then
k2=i1
exit
end if
end do
if(k2.gt.0)then
if(k2+k1+2.lt.len(qerrmsg))then
qerrmsg(k2:k2+k1+3)=achar(aspc)//achar(alsbr)//stcb(j1:j1+k1-1)//achar(arsbr)//achar(anull)
end if
end if
end if
end if
end if
k1=k3
k2=k4
call qmput(k1,k2,ifile)
Q_ERRT
99 continue
return
end subroutine qstymsg
subroutine qiomsg(jj,k3,k4,jfile)
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::k3,k4,jj,jfile
integer(kind=c_int_least32_t)::k1,k2,ifile
ifile=jfile
select case(jj)
case(1)
qerrmsg(1:srec)="system/filesystem I/O error"//achar(anull)
ifile=0
case(2)
qerrmsg(1:srec)="memory (de-)allocation error"//achar(anull)
ifile=0
case(3)
qerrmsg(1:srec)="command-line argument is too long or could not be retrieved"//achar(anull)
ifile=0
case(4)
qerrmsg(1:srec)="problematic command-line options/arguments"//achar(anull)
ifile=0
case(6)
qerrmsg(1:srec)="missing command-line option"//achar(anull)
ifile=0
case(7)
qerrmsg(1:srec)="is already open (or a duplicate)"//achar(anull)
ifile=-jfile
case(8)
qerrmsg(1:srec)="already exists"//achar(anull)
ifile=-jfile
case(9)
qerrmsg(1:srec)="could not be opened"//achar(anull)
ifile=-jfile
case(11)
qerrmsg(1:srec)="could not be closed"//achar(anull)
ifile=-jfile
case(12)
qerrmsg(1:srec)="could not be found"//achar(anull)
ifile=-jfile
case(13)
qerrmsg(1:srec)="forbidden filename/directory/path for"//achar(anull)
case(14)
qerrmsg(1:srec)="wrong syntax or unexpected statement,"//achar(anull)
case(16)
qerrmsg(1:srec)="more than one kind of annotation-mark used,"//achar(anull)
ifile=jfile
case(17)
qerrmsg(1:srec)="forbidden characters in"//achar(anull)
case(18)
qerrmsg(1:srec)="some string is too long"//achar(anull)
case(19)
qerrmsg(1:srec)="line too long or wrongly-terminated,"//achar(anull)
case(21)
qerrmsg(1:srec)="'large' integer read or generated"//achar(anull)
case(23)
qerrmsg(1:srec)="obsolescent syntax,"//achar(anull)
case default
qerrt(0)=qerrty%q
qerrmsg(1:srec)="qiomsg_1"//achar(anull)
end select
k1=k3
k2=k4
call qmput(k1,k2,ifile)
Q_ERRT
99 continue
return
end subroutine qiomsg
subroutine qstap(ia,ib,jf)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(inout)::ia,ib
integer(kind=c_int_least32_t),intent(in)::jf
integer(kind=c_int_least32_t)::i1,i2,ii,j1,j2,j3,j4,j5,j7,j8,j9,jj
integer(kind=c_int_least32_t)::p0,p1,p2,strs
ii=iachar(stcb(ib:ib))
if((ii.ne.alf).and.&
(ii.ne.anull))then
qerrmsg(1:srec)='qstap_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
p0=stjbs
call qnapa(stcb,ia,ib,jf)
Q_ERRT
p0=p0+1
jj=stjb(p0)
if(jj.le.0)then
go to 80
end if
p1=p0+1
p2=p1+3*(jj-1)
j7=stcbs(1)
j4=p1
j5=0
strs=0
j8=1
do i1=jj-2,0,-1
j3=j4
j4=j4+3
ii=1
if(stjb(j3).eq.strty%sqs)then
if(stjb(j4).eq.strty%sqs)then
ii=0
else if(stjb(j4).eq.strty%dqs)then
go to 80
end if
else if(stjb(j3).eq.strty%dqs)then
go to 80
if(stjb(j4).eq.strty%dqs)then
ii=0
else if(stjb(j4).eq.strty%sqs)then
go to 80
end if
end if
if(ii.eq.0)then
if(j5.eq.0)then
if(i1.ne.0)then
j5=j5+1
else
j5=j5-1
end if
j1=j3+1
j2=stjb(j1+1)
ii=j2-stjb(j1)
strs=strs+ii
call qvaocb(strs)
Q_ERRT
if(ii-1.gt.0)then
j8=j8-1
end if
j9=j3
do i2=stjb(j1),j2-1
j7=j7+1
stcb(j7:j7)=stcb(i2:i2)
end do
end if
j2=stjb(j4+1)+1
ii=stjb(j4+2)-j2
if(ii.gt.0)then
j8=j8-1
j9=j4
strs=strs+ii
call qvaocb(strs)
Q_ERRT
do i2=j2,stjb(j4+2)-1
j7=j7+1
stcb(j7:j7)=stcb(i2:i2)
end do
end if
stjb(j3)=0
else
j5=-j5
end if
if(j5.lt.0)then
if(j8.lt.0)then
strs=strs+2
j5=stcbs(1)+1
call qaocb(strs)
Q_ERRT
j7=j7+1
stcb(j7:stcbs(1))=stcb(j5:j5)//achar(anull)
j2=j3+1
stjb(j2)=j5
stjb(j2+1)=j7
else
if(j3.ne.j9)then
stjb(j9)=stjb(j3)
stjb(j3)=0
end if
end if
j5=0
j7=stcbs(1)
j8=1
strs=0
end if
end do
j3=p1-3
j4=j3
do i1=1,jj
j4=j4+3
if(stjb(j4).ne.0)then
j3=j3+3
if(j3.ne.j4)then
stjb(j3)=stjb(j4)
stjb(j3+1)=stjb(j4+1)
stjb(j3+2)=stjb(j4+2)
end if
else
stjb(p0)=stjb(p0)-1
if(stjb(p0).le.0)then
go to 80
end if
end if
end do
if(stjb(p0).ne.jj)then
jj=stjb(p0)
p2=p1+3*(jj-1)
call qaojb(-1)
Q_ERRT
ii=p2-p1+4
call qaojb(ii)
Q_ERRT
end if
p0=stj0+1
ii=0
j1=stj0-1
do i1=1,stjb(p0)
j1=j1+3
if(stjb(j1).gt.1)then
ii=ii+stjb(j1+2)-stjb(j1+1)
else if(stjb(j1).eq.1)then
if(stjb(j1).gt.255)then
ii=ii+1
end if
end if
end do
ii=ii+2*stjb(p0)
j2=stcbs(1)
ia=j2+2
call qaocb(ii+2)
Q_ERRT
j1=stj0-1
do i1=1,stjb(p0)
j1=j1+3
if(stjb(j1).gt.1)then
ii=stjb(j1+2)-stjb(j1+1)+2
stcb(j2+1:j2+ii)=achar(aspc)//stcb(stjb(j1+1):stjb(j1+2))
stjb(j1+1)=j2+2
j2=j2+ii
stjb(j1+2)=j2
else if(stjb(j1).eq.1)then
if(stjb(j1).gt.255)then
ii=3
stcb(j2+1:j2+ii)=achar(aspc)//stcb(stjb(j1+2):stjb(j1+2)+1)
else
ii=2
stcb(j2+1:j2+ii)=achar(aspc)//stcb(stjb(j1+2):stjb(j1+2))
end if
stjb(j1+2)=j2+2
j2=j2+ii
end if
end do
stcb(j2+1:j2+2)=achar(alf)//achar(anull)
ib=j2+1
if(j2+2.ne.stcbs(1))then
qerrmsg(1:srec)='qstap_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
stapi(:)=0
stapis=0
qerrt(0)=qerrty%ok
if(jf.eq.qfty%ctyp)then
call qstapc(jj,p1,p2)
Q_ERRT
else if(jf.eq.qfty%mtyp)then
call qstapm(jj,p1,p2)
Q_ERRT
else
qerrt(0)=qerrty%q
end if
if(qerrt(0).eq.qerrty%ok)then
go to 99
end if
80 continue
stapi(1)=0
99 continue
return
end subroutine qstap
subroutine qstapc(jj,p1,p2)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj,p1,p2
integer(kind=c_int_least32_t)::i1,ij,j1
integer(kind=c_int_least32_t)::q0
if(jj.lt.3)then
go to 80
end if
smat='p;q'//achar(anull)
call qmatcha(p2,p1,smat)
Q_ERRT
smat='sip=q'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
q0=p1+1
ij=0
call qmstr0(stcb,stjb(q0),stjb(q0+1),pisk(0),wisk(0),aisk(0),ij)
Q_ERRT
if(ij.le.0)then
go to 80
end if
ij=stib(cisk(0)+ij)
if(ij.le.0)then
go to 80
end if
stapi(1)=ij
serrt=qerrty%ok
if(jj.eq.3)then
smat='sip=p;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.0)then
go to 80
else
go to 99
end if
end if
if((stapi(1).eq.dekc%msg).or.&
(stapi(1).eq.dekc%mdir).or.&
(stapi(1).eq.dekc%odir).or.&
(stapi(1).eq.dekc%sdir).or.&
(stapi(1).eq.dekc%psep).or.&
(stapi(1).eq.dekc%outp).or.&
(stapi(1).eq.dekc%sty))then
smat='sip=ssp;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.0)then
go to 80
end if
stapi(2)=1
else if((stapi(1).eq.dekc%loop).or.&
(stapi(1).eq.dekc%maxc).or.&
(stapi(1).eq.dekc%off))then
smat='sip=szp;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.0)then
stapi(2)=1
else if(stapi(1).eq.dekc%loop)then
smat='sip=szsiszp;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.0)then
stapi(2)=2
end if
end if
if(jbco(0).ne.0)then
go to 80
end if
else if((stapi(1).eq.dekc%loopk).or.&
(stapi(1).eq.dekc%zerok))then
smat='sip=sip;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.0)then
go to 80
end if
stapi(2)=1
else if(stapi(1).eq.dekc%part)then
smat='sip=(szp^[sz|p(s2p)|p(szp)])p;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).lt.2)then
serrt=qerrty%inp
else if(jbco(1).ne.qmatc%lc)then
serrt=qerrty%inp
else if(jbco(2).lt.1)then
serrt=qerrty%inp
else if(jbco(0).ne.2*(jbco(2)+1))then
serrt=qerrty%inp
end if
j1=2
do i1=1,jbco(2)
j1=j1+1
if(jbco(j1).ne.qmatc%oc)then
serrt=qerrty%inp
end if
j1=j1+1
if(jbco(j1).lt.1)then
serrt=qerrty%inp
else if(jbco(j1).gt.3)then
serrt=qerrty%inp
end if
end do
if(serrt.ne.qerrty%ok)then
go to 80
end if
stapi(2)=2*jbco(2)
else if(stapi(1).eq.dekc%model)then
smat='si[p=sid/|p=]ssp;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
serrt=qerrty%inp
else if(jbco(1).ne.qmatc%oc)then
serrt=qerrty%inp
else if(jbco(2).lt.1)then
serrt=qerrty%inp
else if(jbco(2).gt.2)then
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
stapi(2)=3-jbco(2)
else if((stapi(1).eq.dekc%conf).or.&
(stapi(1).eq.dekc%opt))then
smat='sip=(si\p;\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
serrt=qerrty%inp
else if(jbco(1).ne.qmatc%lc)then
serrt=qerrty%inp
else if(jbco(2).lt.1)then
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
stapi(2)=jbco(2)
else if((stapi(1).eq.dekc%in).or.&
(stapi(1).eq.dekc%out))then
smat='sip=(si\p;\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
serrt=qerrty%inp
else if(jbco(1).ne.qmatc%lc)then
serrt=qerrty%inp
else if(jbco(2).lt.1)then
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
smat='sip=([sip[sip]|sip(sip)]\p;\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
serrt=qerrty%ok
if(jbco(0).ne.2+2*jbco(2))then
serrt=qerrty%inp
else if(jbco(1).ne.qmatc%lc)then
serrt=qerrty%inp
else if(jbco(2).lt.1)then
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
end if
stapi(2)=jbco(2)
else if((stapi(1).eq.dekc%tru).or.&
(stapi(1).eq.dekc%fal))then
smat='sip=sip[(s1p,)szp]p;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).lt.2)then
go to 80
else if(jbco(1).ne.qmatc%lc)then
go to 80
else if(jbco(2).lt.0)then
go to 80
end if
q0=p1+7
ij=0
call qmstr0(stcb,stjb(q0),stjb(q0+1),popt2(0),wopt2(0),aopt2(0),ij)
Q_ERRT
if(ij.le.0)then
go to 80
end if
ij=stib(copt2(0)+ij)
if(ij.le.0)then
go to 80
end if
select case(ij)
case(1:5)
smat='sip=sip[(sip,)szp,szp]p;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
go to 80
else if(jbco(1).ne.qmatc%lc)then
go to 80
else if(jbco(2).lt.0)then
go to 80
end if
stapi(2)=jbco(2)+2
case(6:7)
smat='sip=sip[sip,szp,szp]p;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.0)then
go to 80
end if
stapi(2)=3
case(11)
smat='sip=sip[(szp,)sip,szp,szp]p;'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
go to 80
else if(jbco(1).ne.qmatc%lc)then
go to 80
else if(jbco(2).le.0)then
go to 80
end if
stapi(2)=jbco(2)+2
case(12)
smat='sip=sip[(sz\p]p;\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
go to 80
else if(jbco(1).ne.qmatc%lc)then
go to 80
else if(jbco(2).le.0)then
go to 80
end if
stapi(2)=jbco(2)+1
case default
go to 80
end select
else
go to 80
end if
go to 99
80 continue
stapi(1)=0
qerrt(0)=qerrty%inp
99 continue
return
end subroutine qstapc
subroutine qstapm(jj,p1,p2)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::jj,p1,p2
integer(kind=c_int_least32_t)::i1,ij,ik,j1
integer(kind=c_int_least32_t)::q0,q1
if(jj.lt.3)then
go to 80
end if
smat='p]q'//achar(anull)
call qmatcha(p2,p1,smat)
Q_ERRT
if(jbco(0).ne.0)then
go to 80
end if
q0=0
q1=0
smat='[p[|si]q'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.2)then
if(jbco(1).eq.qmatc%oc)then
if(jbco(2).eq.1)then
go to 301
else if(jbco(2).eq.2)then
go to 304
end if
end if
end if
go to 80
301 continue
smat='p[si[p,|p]]q'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.2)then
if(jbco(1).eq.qmatc%oc)then
if(jbco(2).le.0)then
go to 80
else if(jbco(2).gt.2)then
go to 80
end if
if(jbco(2).eq.1)then
smat='p[sip,sip,[sz|s+|s-]q'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.2)then
if(jbco(1).eq.qmatc%oc)then
if(abs(jbco(2)-2).le.1)then
stapi(1)=dekm%p_def
go to 307
end if
end if
end if
end if
stapi(1)=dekm%v_def
go to 307
end if
end if
if(jj.gt.4)then
smat='p[[d;|p;|]sip=q'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.2)then
if(jbco(1).eq.qmatc%oc)then
if(jbco(2).eq.1)then
stapi(1)=dekm%f_gdft
else if(jbco(2).eq.2)then
stapi(1)=dekm%f_sdft
else if(jbco(2).eq.3)then
stapi(1)=dekm%c_gdef
else
go to 80
end if
go to 307
end if
end if
end if
if(jj.gt.3)then
smat='p[si[si|]d:q'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.2)then
if(jbco(1).eq.qmatc%oc)then
if(jbco(2).eq.1)then
q1=p1+4
q0=q1+3
stapi(2)=1
else if(jbco(2).eq.2)then
q0=p1+4
else
go to 80
end if
go to 307
end if
end if
end if
go to 80
304 continue
q0=p1+1
307 continue
if(q0.gt.0)then
if(stjb(p1).ne.strty%id)then
ik=0
else
ik=1
end if
call qmstr0(stcb,stjb(q0),stjb(q0+1),popt5(0),wopt5(0),aopt5(0),ik)
Q_ERRT
if(ik.le.0)then
go to 80
end if
stapi(1)=stib(copt5(0)+ik)
ij=stib(xopt5(0)+ik)
j1=stjb(q0+1)
j1=iachar(stcb(j1:j1))
if((j1.eq.115).or.&
(j1.eq.83))then
stapis=1
end if
if(stapi(2).eq.0)then
stapi(2)=ij
else
stapi(2)=-ij
end if
end if
if(q1.gt.0)then
ik=0
call qmstr0(stcb,stjb(q1),stjb(q1+1),popt7(0),wopt7(0),aopt7(0),ik)
Q_ERRT
if(ik.le.0)then
go to 80
end if
end if
if(stapi(1).eq.dekm%v_def)then
smat='p[(si\p]\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).lt.0)then
j1=qll(mllty%mvf)%n
if(j1.gt.0)then
smat='p]p;q'//achar(anull)
call qmatcha(p2,p1,smat)
Q_ERRT
if(jbco(0).eq.0)then
smat='p[(si\p;\p,)p]'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
end if
end if
end if
if(jbco(0).eq.2)then
if(jbco(1).eq.qmatc%lc)then
if(jbco(2).gt.0)then
stapi(3)=jbco(2)
end if
end if
end if
if(jbco(0).lt.0)then
smat='p[(si\p;\p,)(sip=s1\p]\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.4)then
if(jbco(1).eq.qmatc%lc)then
if(jbco(2).gt.0)then
if(jbco(3).eq.qmatc%lc)then
if(jbco(4).gt.0)then
stapi(3)=jbco(2)
stapi(4)=jbco(4)
else
go to 80
end if
end if
end if
end if
end if
end if
if(stapi(3).eq.0)then
go to 80
end if
stapi(2)=mllty%mvf
else if(stapi(1).eq.dekm%p_def)then
smat='p[sip,sip,[sz|s+|s-](p,si)p]'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).lt.0)then
j1=(qll(mllty%mff)%n)+(qll(mllty%mpf)%n)
if(j1.gt.0)then
smat='p]p;q'//achar(anull)
call qmatcha(p2,p1,smat)
Q_ERRT
if(jbco(0).eq.0)then
smat='p[sip,sip,[sz|s+|s-](p,si)p;p]'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
end if
end if
end if
if(jbco(0).lt.0)then
smat='p[sip,sip,[sz|s+|s-](p,si)p;'//'(sip=[s1|p(s1p)|p(s1p,s1p)]\p]\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
end if
serrt=qerrty%ok
if(jbco(0).lt.4)then
serrt=qerrty%inp
else if(jbco(1).ne.qmatc%oc)then
serrt=qerrty%inp
else if(abs(jbco(2)-2).gt.1)then
serrt=qerrty%inp
else if(jbco(3).ne.qmatc%lc)then
serrt=qerrty%inp
else if(jbco(4).lt.0)then
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
if(jbco(0).eq.4)then
stapi(3)=3+jbco(4)
else
if(jbco(5).ne.qmatc%lc)then
serrt=qerrty%inp
else if(jbco(6).lt.0)then
serrt=qerrty%inp
else if(jbco(0)-6.ne.2*jbco(6))then
serrt=qerrty%inp
end if
if(serrt.ne.qerrty%ok)then
go to 80
end if
j1=6
do i1=1,jbco(6)
j1=j1+1
if(jbco(j1).ne.qmatc%oc)then
serrt=qerrty%inp
end if
j1=j1+1
if(abs(jbco(j1)-2).gt.1)then
serrt=qerrty%inp
end if
end do
if(serrt.ne.qerrty%ok)then
go to 80
end if
stapi(3)=3+jbco(4)
stapi(4)=jbco(6)
end if
stapi(2)=mllty%mpf
else if((stapi(1).eq.dekm%c_stm).or.&
(stapi(1).eq.dekm%f_stm))then
if(stapi(2).gt.0)then
smat='p[sid:(si\p]\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
go to 80
else if(jbco(1).ne.qmatc%lc)then
go to 80
else if(jbco(2).lt.1)then
go to 80
end if
else if(stapi(2).lt.0)then
smat='p[sisid:(si\p]\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
go to 80
else if(jbco(1).ne.qmatc%lc)then
go to 80
else if(jbco(2).lt.0)then
go to 80
end if
else
go to 80
end if
stapi(3)=jbco(2)
else if(stapi(1).eq.dekm%c_gdef)then
smat='p[sip=s1p]'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.0)then
go to 80
end if
stapi(3)=2
else if((stapi(1).eq.dekm%f_gdft).or.&
(stapi(1).eq.dekm%f_sdft))then
smat='p[[d;|p;]sip=[s1|p(s1p)|p(s1p,s1p)]'//'[p,p(s1p)|p,p(s1p,s1p)|]p]'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.6)then
if(jbco(1).eq.qmatc%oc)then
if(jbco(3).eq.qmatc%oc)then
if((jbco(4).eq.1).and.&
(jbco(6).eq.3))then
stapi(3)=2
else if((jbco(4).eq.2).and.&
(jbco(6).eq.2))then
stapi(3)=4
stapi(4)=3
else if((jbco(4).eq.2).and.&
(jbco(6).eq.3))then
stapi(3)=2
stapi(4)=2
else if((jbco(4).eq.3).and.&
(jbco(6).eq.1))then
stapi(3)=4
stapi(4)=4
else if((jbco(4).eq.3).and.&
(jbco(6).eq.3))then
stapi(3)=3
stapi(4)=1
else
go to 80
end if
end if
end if
end if
if(stapi(3).eq.0)then
go to 80
end if
else if((stapi(1).eq.dekm%sbm_stm).or.&
(stapi(1).eq.dekm%sk_stm))then
smat='p[sid:(si\p]\p,)'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.2)then
go to 80
else if(jbco(1).ne.qmatc%lc)then
go to 80
else if(jbco(2).lt.1)then
go to 80
end if
stapi(3)=jbco(2)
else if((stapi(1).eq.dekm%sbmb_stm).or.&
(stapi(1).eq.dekm%sbmb_end).or.&
(stapi(1).eq.dekm%skb_stm))then
smat='sip[sip]'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).ne.0)then
go to 80
end if
stapi(3)=1
else if(stapi(1).eq.dekm%sbmb_sk)then
smat='p[sid:[p]|(si\p]\p,)]'//achar(anull)
call qmatcha(p1,p2,smat)
Q_ERRT
if(jbco(0).eq.2)then
if(jbco(1).ne.qmatc%oc)then
go to 80
else if(jbco(2).ne.1)then
go to 80
end if
stapi(3)=0
else if(jbco(0).eq.4)then
if(jbco(1).ne.qmatc%oc)then
go to 80
else if(jbco(2).ne.2)then
go to 80
else if(jbco(3).ne.qmatc%lc)then
go to 80
else if(jbco(4).lt.1)then
go to 80
end if
stapi(3)=jbco(4)
else
go to 80
end if
else
go to 80
end if
go to 99
80 continue
stapi(1)=0
qerrt(0)=qerrty%inp
99 continue
return
end subroutine qstapm
subroutine qaocb(delta)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::delta
integer(kind=c_int_least32_t)::ii,jj,kk
if(delta.gt.0)then
jj=(stcbas(1)-stcbs(1))-delta
kk=stcbdst(1)
do while((jj.lt.0).and.&
(kk.lt.stcbdst0))
kk=kk+1
jj=(scbff(kk)-dcff0-stcbs(1))-delta
end do
if(jj.lt.0)then
qerrt(0)=qerrty%q
call quput(6)
Q_ERRT
else if(kk.gt.stcbdst(1))then
stcbdst(1)=kk
ii=scbff(kk)+1
if(.not.allocated(ystcb))then
allocate(character(len=ii)::ystcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
ystcb(1:stcbas(1))=xstcb(1:stcbas(1))
xstcb(1:stcbas(1))=achar(anull)
if(iachar(xstcb(kk:kk)).ne.anull)then
qerrmsg(1:srec)='qaocb_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
stcb=>ystcb
deallocate(xstcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
else if(.not.allocated(xstcb))then
allocate(character(len=ii)::xstcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
xstcb(1:stcbas(1))=ystcb(1:stcbas(1))
ystcb(1:stcbas(1))=achar(anull)
if(iachar(ystcb(kk:kk)).ne.anull)then
qerrmsg(1:srec)='qaocb_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
stcb=>xstcb
deallocate(ystcb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
else
qerrmsg(1:srec)='qaocb_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
stcbas(1)=ii-dcff0
end if
stcbs(1)=stcbs(1)+delta
else if(delta.lt.0)then
stcbs(1)=stcbs(1)+delta
if(stcbs(1).lt.0)then
qerrmsg(1:srec)='qaocb_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
99 continue
return
end subroutine qaocb
subroutine qvaocb(delta)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::delta
if((delta.lt.0).or.&
(stcbs(1).lt.0))then
qerrmsg(1:srec)='qvaocb_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
else if((stcbas(1)-stcbs(1)).lt.delta)then
call qaocb(delta)
Q_ERRT
call qaocb(-delta)
Q_ERRT
end if
99 continue
return
end subroutine qvaocb
subroutine qlink(p0,delta)
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::delta
integer(kind=c_int_least32_t),intent(inout)::p0
integer(kind=c_int_least32_t)::ii,p1
if((delta.le.0).or.&
(stib(stibs(1)).ne.eoa))then
qerrmsg(1:srec)='qlink_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
p1=stibs(1)+1
ii=delta+3
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
if(p0.ne.nap)then
stib(p1)=p0
stib(p0)=p1+1
else
stib(p1)=p1
end if
p0=p1+1
stib(p0)=p0
99 continue
return
end subroutine qlink
subroutine qaoib(delta)
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::delta
integer(kind=c_int_least32_t)::ii,jj,kk
if(delta.gt.0)then
jj=(stibas(1)-stibs(1))-delta
kk=stibdst(1)
do while((jj.lt.0).and.&
(kk.lt.stibdst0))
kk=kk+1
jj=(sibff(kk)-diff0-stibs(1))-delta
end do
if(jj.lt.0)then
qerrt(0)=qerrty%q
call quput(4)
Q_ERRT
else if(kk.gt.stibdst(1))then
stibdst(1)=kk
ii=sibff(kk)+1
if(.not.allocated(ystib))then
allocate(ystib(ii),stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
ystib(1:stibas(1))=xstib(1:stibas(1))
xstib(1:stibas(1))=0
if(xstib(kk).ne.0)then
qerrmsg(1:srec)='aoib_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
stib=>ystib
deallocate(xstib,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
else if(.not.allocated(xstib))then
allocate(xstib(ii),stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
xstib(1:stibas(1))=ystib(1:stibas(1))
ystib(1:stibas(1))=0
if(ystib(kk).ne.0)then
qerrmsg(1:srec)='aoib_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
stib=>xstib
deallocate(ystib,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
else
qerrmsg(1:srec)='aoib_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
stibas(1)=ii-diff0
end if
stibs(1)=stibs(1)+delta
else if(delta.lt.0)then
stibs(1)=stibs(1)+delta
if(stibs(1).lt.0)then
qerrmsg(1:srec)='aoib_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
99 continue
return
end subroutine qaoib
subroutine qaojb(delta)
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::stj1=stj0-1
integer(kind=c_int_least32_t),parameter::sjb0=sjbuff0-stj0
integer(kind=c_int_least32_t),intent(in)::delta
integer(kind=c_int_least32_t)::dd,ii,jj,kk
jj=stjbs
if(jj.lt.0)then
go to 80
else if(jj.lt.stj0)then
go to 80
else if(jj.gt.sjbuff0)then
go to 80
end if
ii=stjb(jj)
if(ii.gt.0)then
go to 80
else if(ii.ne.eoa)then
go to 80
end if
ii=stjb(jj-1)
if(ii.gt.0)then
go to 80
else if(ii.ne.nap)then
go to 80
end if
ii=stjb(jj-stj1)
if(ii.gt.0)then
go to 80
else if(ii.ne.eoa)then
go to 80
end if
if(delta.gt.0)then
if(delta.le.sjb0)then
dd=delta+stj0
kk=(sjbuff0-jj)-dd
if(kk.ge.0)then
go to 10
end if
end if
qerrt(0)=qerrty%q
call quput(5)
Q_ERRT
10 continue
stjbs=jj+dd
stjb(jj-1)=stjbs
stjb(stjbs)=eoa
stjb(stjbs-1)=nap
stjb(stjbs-2)=jj
stjb(stjbs-stj1)=eoa
nstjb=nstjb+1
go to 99
else if(delta+1.eq.0)then
kk=stjb(jj-2)
if(kk.lt.0)then
go to 80
else if(kk-stj0.lt.0)then
go to 80
else if(kk-sjb0.gt.0)then
go to 80
else if(kk-(jj-stj0).gt.0)then
go to 80
end if
ii=stjb(kk)
if(ii.gt.0)then
go to 80
else if(ii.ne.eoa)then
go to 80
end if
ii=stjb(kk-1)
if(ii.lt.0)then
go to 80
else if(ii.ne.stjbs)then
go to 80
end if
ii=stjb(kk-stj1)
if(ii.gt.0)then
go to 80
else if(ii.ne.eoa)then
go to 80
end if
stjbs=kk
stjb(kk-1)=nap
nstjb=nstjb-1
go to 99
end if
80 continue
qerrmsg(1:srec)='qaojb_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
99 continue
return
end subroutine qaojb
subroutine qaosb(delta)
use,non_intrinsic::qfcon
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),parameter::sts1=sts0-1
integer(kind=c_int_least32_t),parameter::sb0=sjbuff0-sts0
integer(kind=c_int_least32_t),intent(in)::delta
integer(kind=c_int_least32_t)::dd,ii,jj,kk
jj=stsbs
if(jj.lt.0)then
go to 80
else if(jj.lt.sts0)then
go to 80
else if(jj.gt.sjbuff0)then
go to 80
end if
ii=stsb(jj)
if(ii.gt.0)then
go to 80
else if(ii.ne.eoa)then
go to 80
end if
ii=stsb(jj-1)
if(ii.gt.0)then
go to 80
else if(ii.ne.nap)then
go to 80
end if
ii=stsb(jj-sts1)
if(ii.gt.0)then
go to 80
else if(ii.ne.eoa)then
go to 80
end if
if(delta.gt.0)then
if(delta.le.sb0)then
dd=delta+sts0
kk=(sjbuff0-jj)-dd
if(kk.ge.0)then
go to 10
end if
end if
qerrt(0)=qerrty%q
call quput(5)
Q_ERRT
10 continue
stsbs=jj+dd
stsb(jj-1)=stsbs
stsb(stsbs)=eoa
stsb(stsbs-1)=nap
stsb(stsbs-2)=jj
stsb(stsbs-sts1)=eoa
nstsb=nstsb+1
go to 99
else if(delta+1.eq.0)then
kk=stsb(jj-2)
if(kk.lt.0)then
go to 80
else if(kk-sts0.lt.0)then
go to 80
else if(kk-sb0.gt.0)then
go to 80
else if(kk-(jj-sts0).gt.0)then
go to 80
end if
ii=stsb(kk)
if(ii.gt.0)then
go to 80
else if(ii.ne.eoa)then
go to 80
end if
ii=stsb(kk-1)
if(ii.lt.0)then
go to 80
else if(ii.ne.stsbs)then
go to 80
end if
ii=stsb(kk-sts1)
if(ii.gt.0)then
go to 80
else if(ii.ne.eoa)then
go to 80
end if
stsbs=kk
stsb(kk-1)=nap
nstsb=nstsb-1
go to 99
end if
80 continue
qerrmsg(1:srec)='qaosb_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
99 continue
return
end subroutine qaosb
subroutine qvaoib(delta)
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::delta
if((delta.le.0).or.&
(stibs(1).lt.0))then
qerrmsg(1:srec)='qvaoib_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
else
if((stibas(1)-stibs(1)).lt.delta)then
call qaoib(delta)
Q_ERRT
call qaoib(-delta)
Q_ERRT
end if
end if
99 continue
return
end subroutine qvaoib
subroutine qvaojb(delta)
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::delta
if((delta.le.0).or.&
(stjbs.le.0))then
qerrmsg(1:srec)='qvaojb_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(delta.gt.sjbuff0-stjbs)then
qerrt(0)=qerrty%q
call quput(5)
Q_ERRT
end if
99 continue
return
end subroutine qvaojb
#undef Q_ERRT
#define Q_ERRT !
subroutine qmput(nl1,nl2,nf1)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qwztos
integer(kind=c_int_least32_t),intent(in)::nl1,nl2,nf1
integer(kind=c_int_least32_t),parameter::leftab=3
integer(kind=c_int_least32_t)::cf1,cf2,cf3,cf4,nfx,slin2,slin3,f0,wf0
integer(kind=c_int_least32_t)::i1,i2,j1,j2,j3,j4,j5,jj,k1,k2,k3,k4,k5
character(kind=asciik,len=qerrl0)::msg
if(qerrt(2).lt.qerrt(0))then
qerrt(2)=qerrt(0)
else if(qerrt(2).gt.qerrty%ale)then
go to 99
end if
call qsp(0,0,0)
Q_ERRT
jflag(jflaty%nw)=min(jflag(jflaty%nw)+1,zbo%iref)
f0=non_unit
wf0=0
if(cflag(confi%msg).gt.0)then
do i1=1,nfiles
if(filt(i1).eq.qfty%wtyp)then
if(filu(i1).ne.non_unit)then
if(filp(i1).ne.nap)then
f0=filu(i1)
end if
end if
exit
end if
end do
end if
if(qxmod.eq.qmod%api)then
if(cflag(confi%dspl).eq.dsplmod%dbg)then
cf1=1
else
cf1=0
end if
else
if(qerrt(0).gt.qerrty%ale)then
cf1=1
else if(cflag(confi%dspl).gt.dsplmod%info)then
cf1=1
else
cf1=0
end if
end if
if(cflag(confi%msg).eq.0)then
cf2=0
else if(f0.eq.non_unit)then
cf2=0
else
cf2=1
end if
cf3=0
if(cflag(confi%msg).eq.0)then
if(qerrt(0).eq.qerrty%ale)then
if(qxmod.ne.qmod%fcon)then
cf3=1
if(.not.allocated(stmb))then
allocate(character(len=sxbuff0+1)::stmb,stat=mas)
if(mas.ne.0)then
call qmas
Q_ERRT
end if
end if
end if
end if
end if
cf4=0
if(qxmod.eq.qmod%api)then
if(qerrt(0).gt.qerrty%ale)then
cf4=1
end if
end if
serrt=qerrty%ok
if(nl1.lt.0)then
serrt=qerrty%q
else if(nl2.lt.nl1)then
serrt=qerrty%q
else if(abs(nf1).gt.nfiles)then
nfx=nf1-mfiles0
if(nfx.lt.0)then
serrt=qerrty%q
else if(nfx.gt.qfty%ubo)then
serrt=qerrty%q
end if
else if(nf1.ne.0)then
nfx=filt(abs(nf1))
if(nfx.le.0)then
serrt=qerrty%q
else if(nfx.ge.qfty%ptyp)then
serrt=qerrty%q
end if
end if
if(serrt.gt.qerrt(0))then
qerrt(0)=serrt
if(qxmod.eq.qmod%api)then
qerrmsg(1:srec)=blak(1:leftab)//" qmput_1"//achar(anull)
go to 99
else
dmsg=achar(alf)//blak(1:leftab)//" qmput_1"//achar(alf)//achar(anull)
call qdwout(error_unit,sdrec,leftab)
Q_ERRT
if(cf2.gt.0)then
call qdwout(f0,sdrec,leftab)
Q_ERRT
dmsg(1:sdrec-1)=sthb2(2:sdrec-1)//achar(anull)
call qdwout(f0,sdrec,0)
Q_ERRT
end if
call qstop
Q_ERRT
end if
end if
if(qerrt(0).le.qerrty%ale)then
k1=stib(xtstrp(0)+33)
k2=stib(xtstrl(0)+33)
else
k1=stib(mprep(0)+qerrt(0))
k2=stib(mprel(0)+qerrt(0))
end if
k3=k1+(k2-1)
slin2=srecx
slin3=(stcbas(1)-zbo%wiref)-stcbs(1)
if(cf1.gt.0)then
if(qerrt(0).gt.qerrty%ale)then
dmsg(1:sdrec+2)=achar(alf)//achar(alf)//sthb2(1:sdrec-1)//achar(anull)
call qdwout(error_unit,sdrec,0)
Q_ERRT
end if
end if
j1=0
j2=0
do i1=1,qerrl0
if(iachar(qerrmsg(i1:i1)).eq.anull)then
j1=1
j2=i1-1
exit
end if
end do
i2=0
if(nf1.ge.0)then
if(j1.gt.0)then
j3=min(slin2-i2,j2-j1+1)
if(j3.gt.0)then
msg(i2+1:i2+j3)=qerrmsg(j1:j1-1+j3)
i2=i2+j3
end if
end if
end if
if(nf1.ne.0)then
if(nf1.gt.0)then
if(i2.lt.slin2)then
i2=i2+1
msg(i2:i2)=blak(1:1)
end if
end if
i1=stib(xgfnl(0)+nfx)
if(i2+i1.le.slin2)then
j3=stib(xgfnp(0)+nfx)
msg(i2+1:i2+i1)=stcb(j3:j3-1+i1)
end if
i2=i2+i1
if(nsfiles.gt.1)then
if((nfx.eq.qfty%styp).or.&
(nfx.eq.qfty%otyp))then
if(i2.lt.slin2+1)then
i2=i2+2
msg(i2-1:i2)=achar(aspc)//achar(ahash)
end if
nfx=film(abs(nf1))
nfx=min(max(0,nfx),sfiles0+1)
call qxdkar(nfx,jj)
Q_ERRT
j5=i2+jj
if(j5.le.slin2)then
if(j5.lt.qerrl0)then
msg(i2+1:i2+jj)=zstr(1:jj)
i2=j5
end if
end if
end if
end if
end if
if(nf1.lt.0)then
if(j2.gt.0)then
if(j2-j1+2.le.slin2-i2)then
msg(i2+1:i2+2+(j2-j1))=blak(1:1)//qerrmsg(j1:j2)
i2=i2+(j2-j1)+2
end if
end if
end if
if(nl1.gt.0)then
if(nl1.eq.nl2)then
i1=stib(xtstrl(0)+30)
if(i2+i1.le.slin2)then
j3=stib(xtstrp(0)+30)
msg(i2+1:i2+i1)=stcb(j3:j3-1+i1)
end if
i2=i2+i1
call qxdkar(nl1,jj)
Q_ERRT
j5=i2+jj
if(j5.le.slin2)then
if(j5.lt.qerrl0)then
if(slin3.ge.0)then
msg(i2+1:i2+jj)=zstr(1:jj)
i2=j5
end if
else
i1=stib(xtstrl(0)+32)
j3=stib(xtstrp(0)+32)
msg(i2+1:i2+i1)=stcb(j3:j3-1+i1)
i2=i2+i1
end if
end if
else
i1=stib(xtstrl(0)+31)
if(i2+i1.le.slin2)then
j3=stib(xtstrp(0)+31)
msg(i2+1:i2+i1)=stcb(j3:j3-1+i1)
end if
i2=i2+i1
call qxdkar(nl1,jj)
Q_ERRT
j5=i2+jj
if(j5.le.slin2)then
if(j5.lt.qerrl0)then
if(slin3.ge.0)then
msg(i2+1:i2+jj)=zstr(1:jj)
i2=j5
end if
else
i1=stib(xtstrl(0)+32)
j3=stib(xtstrp(0)+32)
msg(i2+1:i2+i1)=stcb(j3:j3-1+i1)
i2=i2+i1
end if
end if
if(i2+1.le.slin2)then
msg(i2+1:i2+1)=achar(aminus)
end if
i2=i2+1
call qxdkar(nl2,jj)
Q_ERRT
j5=i2+jj
if(j5.le.slin2)then
if(j5.lt.qerrl0)then
if(slin3.ge.0)then
msg(i2+1:i2+jj)=zstr(1:jj)
i2=j5
end if
else
i1=stib(xtstrl(0)+32)
j3=stib(xtstrp(0)+32)
msg(i2+1:i2+i1)=stcb(j3:j3-1+i1)
i2=i2+i1
end if
end if
end if
end if
if(cf1.gt.0)then
j2=0
if(qerrt(0).le.qerrty%ale)then
j2=2
dmsg(1:j2)=achar(alf)//achar(alf)
j5=j2+k2
dmsg(j2+1:j5)=stcb(k1:k3)
j2=j5
else if(cflag(confi%dspl).ne.dsplmod%noinfo)then
j5=j2+leftab+k2
dmsg(j2+1:j5)=blak(1:leftab)//stcb(k1:k3)
j2=j5
else
j3=stib(mprep(0)+5)
j4=stib(mprel(0)+5)
if(qvl.eq.0)then
j5=j2+leftab+j4+k2
dmsg(j2+1:j5)=blak(1:leftab)//stcb(j3:(j3-1)+j4)//stcb(k1:k3)
else
k4=stib(xtstrp(0)+34)
k5=stib(xtstrl(0)+34)
j5=j2+leftab+qvl+k2+k5
k5=k4+(k5-1)
dmsg(j2+1:j5)=blak(1:leftab)//stcb(qvp:(qvp-1)+qvl)//stcb(k4:k5)//stcb(k1:k3)
end if
j2=j5
end if
j5=j2+i2+1
dmsg(j2+1:j5)=msg(1:i2)//achar(anull)
j2=j5
if(qerrt(0).eq.qerrty%ale)then
j5=j2+2
dmsg(j2:j5)=achar(alf)//achar(alf)//achar(anull)
j2=j5
end if
call qdwout(error_unit,sdrec,leftab)
Q_ERRT
end if
if(cf2+cf3+cf4.gt.0)then
if(cf2.gt.0)then
jflag(jflaty%nwf)=min(jflag(jflaty%nwf)+1,zbo%iref)
if(qerrt(0).eq.qerrty%ale)then
dmsg=blak(1:leftab)//msg(1:i2)//achar(anull)
call qdwout(f0,sdrec,leftab)
Q_ERRT
else
dmsg=blak(1:leftab)//stcb(k1:k3)//msg(1:i2)//achar(anull)
call qdwout(f0,sdrec,leftab)
Q_ERRT
end if
wf0=1
else if(cf3.gt.0)then
if(qerrt(0).eq.qerrty%ale)then
if(allocated(stmb))then
j4=stmbs(1)+i2+1
if(j4.lt.len(stmb)-4)then
stmb(stmbs(1)+1:j4)=msg(1:i2)//achar(anull)
stmbs(1)=j4
else if(stmbs(1).lt.len(stmb)-4-leftab)then
j4=stmbs(1)+4+leftab
stmb(stmbs(1)+1:j4)=blak(1:leftab)//"..."//achar(anull)
stmbs(1)=j4
end if
end if
end if
end if
if(cf4.gt.0)then
if(i2.lt.srec)then
qerrmsg(1:i2+1)=msg(1:i2)//achar(anull)
else
qerrmsg(1:srec)=msg(1:sdrec-4)//'...'//c_null_char
end if
end if
end if
70 continue
if(cf1.gt.0)then
if(qerrt(0).gt.qerrty%ale)then
dmsg(1:sdrec+2)=sthb2(1:sdrec-1)//achar(alf)//achar(alf)//achar(anull)
else
dmsg(1:2)=achar(alf)//achar(anull)
end if
call qdwout(error_unit,sdrec,0)
Q_ERRT
end if
if(cf2.gt.0)then
dmsg(1:sdrec)=sthb2(2:sdrec)//achar(anull)
call qdwout(f0,sdrec,0)
Q_ERRT
wf0=1
end if
80 continue
if(qerrt(0).gt.qerrty%ale)then
if(qerrt(0).lt.qerrty%os)then
call qclose(0)
Q_ERRT
end if
call qstop
Q_ERRT
end if
99 continue
if(qerrt(0).eq.qerrty%ale)then
qerrt(0)=qerrty%ok
end if
return
end subroutine qmput
#undef Q_ERRT
#ifdef Q_API
#define Q_ERRT \
if(qerrt(0).gt.qerrty%ale)then ; \
go to 99 ; \
end if
#else
#define Q_ERRT !
#endif
subroutine quput(ind)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qintr
use,non_intrinsic::qkeys
use,non_intrinsic::qwbuffer
#ifdef Q_API
#endif
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::ind
integer(kind=c_int_least32_t),parameter::leftab=3
integer(kind=c_int_least32_t)::i1,ii,jj
if(qerrt(0).lt.qerrty%q)then
qerrt(0)=qerrty%q
end if
select case(ind)
case(0)
qerrmsg(1:srec)="memory (de-)allocation error"//achar(anull)
case(1)
qerrmsg(1:srec)="system/filesystem I/O error"//achar(anull)
case(2)
qerrmsg(1:srec)="ASCII character set not supported"//achar(anull)
case(3)
qerrmsg(1:srec)="largest available integer is too small"//achar(anull)
case(4)
qerrmsg(1:srec)="parameter 'sibuff0' too small"//achar(anull)
case(5)
qerrmsg(1:srec)="parameter 'sjbuff0' too small"//achar(anull)
case(6)
qerrmsg(1:srec)="parameter 'scbuff0' too small"//achar(anull)
case(7)
qerrmsg(1:srec)="parameter 'swbuff0' too small"//achar(anull)
case(8)
qerrmsg(1:srec)="parameter 'sxbuff0' too small"//achar(anull)
case(9)
qerrmsg(1:srec)="parameter 'sibuff0' not properly set"//achar(anull)
case(10)
qerrmsg(1:srec)="parameter 'sjbuff0' not properly set"//achar(anull)
case(11)
qerrmsg(1:srec)="parameter 'scbuff0' not properly set"//achar(anull)
case(12)
qerrmsg(1:srec)="parameter 'swbuff1' not properly set"//achar(anull)
case(13)
qerrmsg(1:srec)="parameter 'sxbuff0' not properly set"//achar(anull)
case(14)
qerrmsg(1:srec)="parameter 'srec' not properly set"//achar(anull)
case(15)
qerrmsg(1:srec)="parameter 'srecx' not properly set"//achar(anull)
case(16)
qerrmsg(1:srec)="parameter 'sdrec' not properly set"//achar(anull)
case(17)
qerrmsg(1:srec)="parameter 'ptenp' not properly set"//achar(anull)
case default
qerrmsg(1:srec)='quput_1'//achar(anull)
end select
jj=0
do i1=1,len(qerrmsg)
if(iachar(qerrmsg(i1:i1)).eq.anull)then
jj=i1-1
exit
end if
end do
if(qxmod.ne.qmod%api)then
ii=min(sdrec-1,len(dmsg)-2)
if(ii.gt.0)then
dmsg(1:ii+2)=achar(alf)//sthb2(1:ii)//achar(anull)
call qdwout(error_unit,sdrec,0)
Q_ERRT
end if
end if
if(qvl.gt.0)then
dmsg=" "//stcb(qvp:(qvp-1)+qvl)//"::error: "//qerrmsg(1:jj)//achar(anull)
else
dmsg=" qgraf::error: "//qerrmsg(1:jj)//achar(anull)
end if
call qdwout(error_unit,sdrec,leftab)
Q_ERRT
if(qxmod.ne.qmod%api)then
if(ii.gt.0)then
dmsg(1:ii+2)=sthb2(1:ii)//achar(alf)//achar(anull)
call qdwout(error_unit,sdrec,0)
Q_ERRT
end if
end if
call qclose(0)
Q_ERRT
call qstop
Q_ERRT
99 continue
return
end subroutine quput
subroutine qcyc(xx,situ)
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::xx
integer(kind=c_int_least32_t),intent(out)::situ
integer(kind=c_int_least32_t)::i1,i2,i3,j1,j2,j3,jj,k1,k2,kk
integer(kind=c_int_least32_t)::bb(1:maxli),cc(1:maxli)
if(xx.eq.1)then
if(nloop-1.le.0)then
situ=1
go to 99
end if
else
qerrmsg(1:srec)='qcyc_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
j1=0
do i1=rhop1,nli
if(flow(i1,0).lt.0)then
j1=j1+1
bb(j1)=j1
cc(j1)=i1
end if
end do
jj=1-net(-3)
if(jj.lt.0)then
k1=1
k2=net(-3)
d01: do i1=1,net(-3)
j1=cc(i1)
do i2=i1+1,net(-3)
if(bb(i1).ne.bb(i2))then
kk=0
j2=cc(i2)
do i3=rhop1,rhop2
if(flow(j1,i3).ne.0)then
if(flow(j2,i3).ne.0)then
kk=1
exit
end if
end if
end do
if(kk.ne.0)then
if(bb(k1).eq.1)then
k1=k1+1
end if
if(bb(k2).eq.1)then
k2=k2-1
end if
j2=min(bb(i1),bb(i2))
j3=max(bb(i1),bb(i2))
do i3=k1,k2
if(bb(i3).eq.j3)then
bb(i3)=j2
end if
end do
jj=jj+1
if(jj.eq.0)then
exit d01
end if
end if
end if
end do
end do d01
end if
if(jj.lt.0)then
situ=-1
else
situ=1
end if
99 continue
return
end subroutine qcyc
subroutine qrstm(enstm,enlin,edbl,ja,jb)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(inout)::enstm,edbl,enlin,ja,jb
integer(kind=c_int_least32_t)::dbl,stloop,ier,ifile,instm,nlin,nstm,slin,tsl
integer(kind=c_int_least32_t)::i1,j1,j2
if(enstm.eq.1)then
ifile=0
do i1=nfiles,1,-1
if(filt(i1).eq.qfty%mtyp)then
ifile=i1
call qopen(ifile)
Q_ERRT
exit
end if
end do
nstm=0
nlin=0
end if
instm=0
tsl=0
dbl=0
stloop=0
ier=0
do while(stloop.eq.0)
call qrr(ifile,nlin)
Q_ERRT
slin=recdty(recty%len)
if(slin.lt.0)then
if(instm.ne.0)then
ier=1
end if
exit
end if
if(instm.ne.0)then
if(slin.eq.0)then
ier=1
exit
else if(recdty(recty%annot).ne.0)then
ier=1
exit
end if
else
if(slin.eq.0)then
cycle
else if(recdty(recty%annot).ne.0)then
cycle
end if
dbl=nlin
end if
if((slin.ge.srec0).or.&
(recdty(recty%tail).eq.abslash))then
if(filw(ifile).eq.0)then
filw(ifile)=1
else if(filw(ifile).lt.0)then
ier=1
exit
end if
else if(recdty(recty%annot).eq.0)then
if(recdty(recty%tail).ne.arsbr)then
if(filw(ifile).eq.0)then
filw(ifile)=-1
else if(filw(ifile).gt.0)then
ier=1
exit
end if
end if
end if
if(qxmod.ne.qmod%fcon)then
if(filw(ifile).lt.0)then
qerrt(0)=qerrty%inp
call qiomsg(14,dbl,nlin,ifile)
Q_ERRT
end if
end if
if(recdty(recty%tail).eq.abslash)then
j1=0
do i1=stcbs(1)+slin-1,stcbs(1)+1,-1
j2=iachar(stcb(i1:i1))
if(j2.ne.aspc)then
j1=stcbs(1)+slin-i1
slin=slin-j1
exit
end if
end do
if(j1.eq.0)then
ier=1
exit
end if
if(dbl.eq.0)then
dbl=nlin
end if
end if
if(slin.eq.0)then
if(instm.ne.0)then
ier=1
exit
end if
cycle
end if
if(instm.eq.0)then
if(dbl.eq.0)then
dbl=nlin
end if
end if
if(recdty(recty%tail).eq.abslash)then
instm=1
else if(recdty(recty%tail).eq.arsbr)then
instm=0
nstm=nstm+1
stloop=1
else
instm=1
end if
if(tsl.eq.0)then
ja=stcbs(1)+1
end if
tsl=tsl+slin+1
if(tsl.gt.sxbuff0)then
qerrt(0)=qerrty%inp
call qmfmsg(1,dbl,nlin)
Q_ERRT
end if
call qaocb(slin+1)
Q_ERRT
stcb(stcbs(1):stcbs(1))=achar(alf)
end do
if(ier.ne.0)then
go to 80
end if
jb=stcbs(1)
call qaocb(1)
Q_ERRT
stcb(stcbs(1):stcbs(1))=achar(anull)
if(dbl.eq.0)then
dbl=nlin
end if
enlin=nlin
edbl=dbl
ier=0
if(enstm.le.0)then
ier=1
else if(enstm.gt.nstm)then
enstm=-nstm
end if
if(ier.ne.0)then
qerrmsg(1:srec)='qrstm_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
80 continue
if(ier.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(2,dbl,nlin)
Q_ERRT
end if
99 continue
return
end subroutine qrstm
subroutine qsmodel(nlin1,nlin2,slin,jxa,jxb)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(inout)::nlin1,nlin2
integer(kind=c_int_least32_t),intent(out)::jxa,jxb,slin
integer(kind=c_int_least32_t), external::qstdz
integer(kind=c_int_least32_t),parameter::llof(0:5)=[5,4,6,8,12,5]
integer(kind=c_int_least32_t),parameter::ffj(1:4,1:6)=reshape([&
0,0,llof(3),3,llof(3)+2,6,&
llof(1),3,0,0,0,0,&
llof(1),3,llof(3),12,llof(3)+2,6,&
llof(1),21,llof(3),-18,llof(3)+2,6]&
,[4,6],order=[2,1])
type(qqll),pointer::qllp
integer(kind=c_int_least32_t)::msc(1:dekm%ubo),mz(1:dekm%ubo,0:2)
integer(kind=c_int_least32_t)::ifile,mz0,styp,sstyp,styp0(0:2)
integer(kind=c_int_least32_t)::nstm,njb,ic1
integer(kind=c_int_least32_t)::i1,i2,i3,j1,j2,j3,j4,j5,j6,j7
integer(kind=c_int_least32_t)::ier,ii,jj,p0,q0,q1,q2,sp1,sp2
integer(kind=c_int_least32_t)::nsekt,sekt0,sekty1,sekty0,sl1
integer(kind=c_int_least32_t)::sekts(0:0),sekta(0:0),sektb(0:0)
integer(kind=c_int_least32_t)::tsm,smod0,smdef0,smdef1,smodc(0:0)
integer(kind=c_int_least32_t)::sts
njb=nstjb
if(nlin2.eq.0)then
nstm=0
styp=0
styp0(0:2)=[0,dekm%sbmb_stm,dekm%skb_stm]
nsekt=0
sekt0=0
sekty0=0
sekty1=0
sl1=0
tsm=0
smod0=0
smdef0=-1
smdef1=0
smodc(0)=nap
sekts(0)=nap
sekta(0)=nap
sektb(0)=nap
ifile=0
do i1=nfiles,1,-1
if(filt(i1).eq.qfty%mtyp)then
ifile=i1
exit
end if
end do
do i1=1,mll0
qllp=>qll(i1)
qllp%dcs=0
qllp%n=0
qllp%p1=nap
qllp%p2=nap
if(i1.eq.mllty%msm)then
qllp%kl=qllkla%klss
else if(i1.eq.mllty%msk)then
qllp%kl=qllkla%klss
else
qllp%kl=qllkla%klcf
end if
end do
msc(:)=0
msc(dekm%sbm_stm)=1
msc(dekm%c_stm)=2
msc(dekm%c_gdef)=3
msc(dekm%c_gdft)=4
msc(dekm%f_stm)=2
msc(dekm%f_gdft)=4
msc(dekm%sbmb_c)=3
msc(dekm%f_sdft)=4
msc(dekm%p_def)=5
msc(dekm%v_def)=5
mz0=0
mz(:,:)=0
mz(dekm%sbm_stm,0)=1
mz(dekm%sk_stm,0)=2
mz(dekm%c_stm,0)=3
mz(dekm%c_gdef,0)=3
mz(dekm%c_gdft,0)=3
mz(dekm%f_stm,0)=4
mz(dekm%f_gdft,0)=4
mz(dekm%sbmb_stm,0)=5
mz(dekm%skb_stm,0)=6
mz(dekm%p_def,0)=7
mz(dekm%v_def,0)=8
mz(dekm%sbmb_sk,1)=1
mz(dekm%sbmb_c,1)=2
mz(dekm%sbmb_end,1)=3
mz(dekm%f_sdft,2)=1
mz(dekm%p_def,2)=2
mz(dekm%v_def,2)=2
mz(dekm%skb_end,2)=3
end if
70 continue
if(jflag(jflaty%nconst).ne.0)then
qllp=>qll(mllty%mc)
j1=qllp%p1
j2=0
do i1=1,qllp%n
j1=stib(j1)
j2=j2+1
if(stib(smodc(0)+j2).ne.0)then
cycle
end if
if(stib(j1+llof(1)).eq.nap)then
j3=j1+1
j4=stib(j3)+(stib(j3+1)-1)
j5=j1+llof(2)
j6=stib(j5+1)
j5=stib(j5)
if(j5.eq.nap)then
qerrt(0)=qerrty%inp
call qmfmsg(26,0,0)
Q_ERRT
end if
j7=(j4-stib(j3))+(j6-j5)+5
jxa=stcbs(1)+1
jxb=jxa+j7
call qaocb(j7+1)
Q_ERRT
stib(smodc(0)+j2)=1
stcb(jxa:stcbs(1))='['//stcb(stib(j3):j4)//'='//stcb(j5:j6)//']'//achar(alf)
jflag(jflaty%nconst)=-1
go to 71
end if
end do
jflag(jflaty%nconst)=0
end if
nstm=nstm+1
call qrstm(nstm,nlin2,nlin1,jxa,jxb)
Q_ERRT
if(nstm.gt.0)then
slin=jxb-jxa
else
nstm=-nstm
slin=-1
go to 700
end if
71 continue
if(jflag(jflaty%nconst).lt.0)then
go to 73
end if
if(njb.lt.nstjb)then
call qaojb(-1)
Q_ERRT
end if
if(styp.eq.dekm%sbmb_end)then
styp0(mz0)=max(styp0(mz0),dekm%sbmb_stm)
else if(styp.eq.dekm%skb_end)then
styp0(mz0)=max(styp0(mz0),dekm%skb_stm)
else
styp0(mz0)=max(styp0(mz0),styp)
end if
call qstap(jxa,jxb,qfty%mtyp)
Q_ERRT
ier=0
if(stapi(1).le.0)then
go to 110
else if(stapi(1).gt.size(msc))then
ier=1
else if(stapi(3).lt.0)then
ier=1
else if(stapi(4).lt.0)then
ier=1
end if
if(ier.ne.0)then
qerrmsg(1:srec)='qsmodel_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(qxmod.eq.qmod%fcon)then
if(jflag(jflaty%mflang).eq.0)then
if(stapi(1).eq.dekm%c_gdef)then
if(nlin34a.eq.0)then
nlin34a=nlin1
end if
nlin34b=nlin2
end if
end if
end if
styp=stapi(1)
sstyp=stapi(2)
if((smod0.eq.0).and.&
(sekt0.eq.0))then
mz0=0
if(styp.eq.dekm%f_sdft)then
styp=dekm%c_gdft
end if
else if(sekt0.eq.0)then
mz0=1
if(styp.eq.dekm%c_gdef)then
styp=dekm%sbmb_c
end if
else if(smod0.eq.0)then
mz0=2
if(styp.eq.dekm%sbmb_end)then
styp=dekm%skb_end
end if
else
go to 110
end if
ier=0
if(mz(styp,mz0).eq.0)then
ier=1
end if
if(styp.eq.dekm%v_def)then
jj=0
else if(styp.eq.dekm%p_def)then
jj=0
else if(styp.eq.dekm%c_gdef)then
jj=0
else
jj=1
end if
if(styp0(0).eq.0)then
jflag(jflaty%mflang)=jj
else
if(jflag(jflaty%mflang).eq.0)then
if(jj.ne.0)then
ier=1
end if
end if
if(mz(styp,mz0).lt.mz(styp0(mz0),mz0))then
if(styp.ne.dekm%skb_stm)then
ier=1
end if
end if
end if
if(ier.ne.0)then
go to 110
end if
if((styp.le.dekm%sbmb_stm).or.&
(styp.gt.dekm%sbmb_end))then
if(smod0.ne.0)then
ier=1
end if
else
if(smod0.eq.0)then
ier=1
end if
end if
if(mz0.eq.1)then
if(styp0(mz0).eq.dekm%sbmb_stm)then
if(styp.ne.dekm%sbmb_sk)then
ier=1
end if
end if
end if
if((styp.le.dekm%skb_stm).or.&
(styp.gt.dekm%skb_end))then
if(sekt0.ne.0)then
ier=1
else if(sekty0.ne.0)then
ier=1
end if
end if
if(ier.ne.0)then
go to 110
end if
if(styp.gt.dekm%sbm_stm)then
if(mflag(mflaty%nsubm).eq.0)then
if(qxmod.ne.qmod%fcon)then
if(cflag(confi%subm).gt.0)then
qerrt(0)=qerrty%inp
call qcfmsg(12,0,0)
Q_ERRT
end if
end if
else if((qxmod.ne.qmod%fcon).or.&
(stofc.lt.0))then
if(cflag(confi%subm).eq.0)then
qerrt(0)=qerrty%inp
call qcfmsg(12,0,0)
Q_ERRT
end if
if(tsm.eq.0)then
if(smodp(0).ne.nap)then
call qkbp(stcb,smodp(0),smodq(0),mllty%msm,j3,j4,tsm)
Q_ERRT
if(tsm.lt.1)then
qerrt(0)=qerrty%inp
call qcfmsg(12,0,0)
Q_ERRT
end if
end if
end if
else if(stofc.gt.0)then
if(tsm.eq.0)then
tsm=1
end if
end if
if(smodc(0).eq.nap)then
if(styp.gt.dekm%c_gdft)then
ii=qll(mllty%mc)%n
if(ii.gt.0)then
smodc(0)=stibs(1)
call qaoib(ii+1)
Q_ERRT
stib(stibs(1))=eoa
end if
end if
end if
end if
if(sekts(0).eq.nap)then
if(nsekt.gt.0)then
if(styp.gt.dekm%sk_stm)then
sekts(0)=stibs(1)
ii=nsekt+1
call qaoib(2*ii)
Q_ERRT
sektb(0)=stibs(1)-ii
if(mflag(mflaty%nsubm).eq.0)then
stib(sekts(0)+1:sektb(0)-1)=1
stib(sektb(0)+1:stibs(1)-1)=0
else
sekta(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(sekts(0)+1:stibs(1)-1)=0
stib(sekta(0))=eoa
end if
stib(sektb(0))=eoa
stib(stibs(1))=eoa
ii=mflag(mflaty%nsubm)+nsekt
if(ii.gt.3)then
ii=ii+3
sekts1(0)=stibs(1)
call qaoib(2*ii)
Q_ERRT
sekts2(0)=stibs(1)-ii
stib(sekts1(0)+1:stibs(1)-1)=0
stib(sekts2(0))=eoa
stib(stibs(1))=eoa
end if
end if
end if
end if
sts=4
j1=stsbs
call qaosb(sts)
Q_ERRT
stsb(j1+1)=styp
stsb(j1+2)=sstyp
stsb(j1+3)=nlin1
stsb(j1+4)=nlin2
fcsc(styp)=fcsc(styp)+1
p0=stjb(stjbs-2)
if((styp.eq.dekm%skb_stm).or.&
(styp.eq.dekm%skb_end))then
ier=0
if(qll(mllty%msk)%n.eq.0)then
ier=1
else if(styp.eq.dekm%skb_end)then
if(sekt0.eq.0)then
ier=1
else if(sekty0.eq.0)then
ier=1
end if
jj=0
if(styp0(mz0).eq.dekm%f_sdft)then
jj=1
else if(styp0(mz0).eq.dekm%skb_stm)then
jj=1
end if
if(jj.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(19,sl1,nlin2)
Q_ERRT
end if
end if
if(ier.ne.0)then
go to 110
end if
q0=p0+9
j1=stjb(q0)
j2=stjb(q0+1)
call qkbp(stcb,j1,j2,mllty%msk,j3,j4,jj)
Q_ERRT
if(jj.lt.1)then
qerrt(0)=qerrty%inp
call qmfmsg(18,nlin1,nlin2)
Q_ERRT
end if
if(styp.eq.dekm%skb_stm)then
if(stib(sekts(0)+jj).lt.1)then
stib(sekts1(0)+jj+1)=nlin1
end if
if(stib(sektb(0)+jj).ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(20,nlin1,nlin2)
Q_ERRT
end if
stib(sektb(0)+jj)=1
sekt0=jj
sekty0=stib(j4+3)
sl1=nlin1
if(sekty0.lt.sekty1)then
go to 110
end if
sekty1=sekty0
else
if(stib(sekts(0)+jj).lt.1)then
stib(sekts2(0)+jj+1)=nlin2
end if
if(jj.ne.sekt0)then
go to 110
end if
styp0(0)=dekm%skb_stm
styp0(mz0)=dekm%skb_stm
sekt0=0
sl1=0
sekty0=0
do i1=1,mll0
qllp=>qll(i1)
if(qllp%kl.ne.qllkla%klcf)then
cycle
else if(i1.eq.mllty%mc)then
cycle
end if
j4=qllp%p1
do i2=1,qllp%n
j4=stib(j4)
j3=j4+llof(1)
stib(j3:j3+1)=nap
if(i1.eq.mllty%mff)then
j3=j4+llof(3)
stib(j3:j3+3)=nap
end if
end do
end do
end if
else if(styp.eq.dekm%sbm_stm)then
qllp=>qll(mllty%msm)
ier=0
if(qllp%dcs.ne.0)then
ier=1
else if(stapi(3).lt.1)then
ier=1
end if
if(ier.ne.0)then
go to 110
end if
if(qllp%n.eq.0)then
qllp%p1=stibs(1)+1
call qaoib(2)
Q_ERRT
stib(stibs(1))=eoa
qllp%p2=qllp%p1
stib(qllp%p2)=eoa
qllp%dcs=1
end if
q0=p0+6
do i1=1,stapi(3)
q0=q0+6
j1=stjb(q0)
j2=stjb(q0+1)
if(qllp%n.ne.0)then
call qkbp(stcb,j1,j2,-qllkla%klss,j3,j4,jj)
Q_ERRT
if(jj.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(23,nlin1,nlin2)
Q_ERRT
end if
end if
j3=stibs(1)+1
ii=llof(5)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
stib(qllp%p2)=j3
stib(j3)=eoa
stib(j3+1)=j1
stib(j3+2)=j2-(j1-1)
stib(j3+3)=0
stib(stibs(1))=eoa
qllp%p2=j3
qllp%n=(qllp%n)+1
end do
mflag(mflaty%nsubm)=qllp%n
else if(styp.eq.dekm%sk_stm)then
if(stapi(3).lt.1)then
go to 110
end if
qllp=>qll(mllty%msk)
if(qllp%n.eq.0)then
qllp%p1=stibs(1)+1
call qaoib(2)
Q_ERRT
stib(stibs(1))=eoa
qllp%p2=qllp%p1
stib(qllp%p2)=eoa
qllp%dcs=1
end if
q0=p0+6
do i1=1,stapi(3)
q0=q0+6
j1=stjb(q0)
j2=stjb(q0+1)
if(nsekt.gt.0)then
call qkbp(stcb,j1,j2,-qllkla%klss,j3,j4,jj)
Q_ERRT
if(jj.ne.0)then
if(j3.eq.mllty%msk)then
qerrt(0)=qerrty%inp
call qmfmsg(20,nlin1,nlin2)
Q_ERRT
else
qerrt(0)=qerrty%inp
call qmfmsg(22,nlin1,nlin2)
Q_ERRT
end if
end if
end if
nsekt=nsekt+1
j3=stibs(1)+1
ii=llof(5)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
stib(qllp%p2)=j3
stib(j3)=eoa
stib(j3+1)=j1
stib(j3+2)=j2-(j1-1)
stib(j3+3)=sstyp
stib(stibs(1))=eoa
qllp%n=(qllp%n)+1
qllp%p2=j3
if(sstyp.eq.mllty%mpf)then
mflag(mflaty%tpskt)=mflag(mflaty%tpskt)+1
else if(sstyp.eq.mllty%mvf)then
mflag(mflaty%tvskt)=mflag(mflaty%tvskt)+1
else
qerrmsg(1:srec)='qsmodel_7'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end do
else if((styp.eq.dekm%sbmb_stm).or.&
(styp.eq.dekm%sbmb_end))then
qllp=>qll(mllty%mc)
ier=0
if(mflag(mflaty%nsubm).eq.0)then
ier=1
else if(nsekt.eq.0)then
ier=1
else if(stapi(3).ne.1)then
ier=1
else if((smodc(0).eq.nap).and.&
(qllp%n.ne.0))then
ier=1
end if
if(ier.ne.0)then
go to 110
end if
if(styp.eq.dekm%sbmb_end)then
if(styp0(mz0).eq.dekm%sbmb_stm)then
qerrt(0)=qerrty%inp
call qmfmsg(24,sl1,nlin2)
Q_ERRT
end if
if(smod0.eq.tsm)then
j1=qllp%p1
do i1=1,qllp%n
j1=stib(j1)
j2=0
if(stib(j1+llof(1)).ne.nap)then
j2=1
else if(stib(j1+llof(2)).ne.nap)then
j2=1
end if
if(j2.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(26,0,0)
Q_ERRT
end if
end do
end if
if(smodc(0).ne.nap)then
j3=0
j4=qllp%p1
do i2=1,qllp%n
j4=stib(j4)
j3=j3+1
if(stib(smodc(0)+j3).lt.0)then
stib(j4+llof(1):j4+llof(1)+1)=nap
end if
end do
end if
else
if(smodc(0).ne.nap)then
stib(smodc(0)+1:smodc(0)+qllp%n)=0
j3=0
j4=qllp%p1
do i2=1,qllp%n
j4=stib(j4)
j3=j3+1
if(stib(j4+llof(1)).ne.nap)then
stib(smodc(0)+j3)=1
end if
end do
end if
sl1=nlin1
end if
q0=p0+9
j1=stjb(q0)
j2=stjb(q0+1)
call qkbp(stcb,j1,j2,mllty%msm,j3,j4,jj)
Q_ERRT
if(jj.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(25,nlin1,nlin2)
Q_ERRT
end if
if(styp.eq.dekm%sbmb_end)then
if(jj.ne.smod0)then
go to 110
end if
stib(j4+3)=1
if((smod0.eq.tsm).and.&
(qllp%n.ne.0))then
jflag(jflaty%nconst)=1
else
jflag(jflaty%nconst)=0
end if
smod0=0
smdef0=-1
smdef1=0
sl1=0
styp0(0)=dekm%sbmb_stm
styp0(mz0)=dekm%sbmb_stm
else
if(stib(j4+3).ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(23,nlin1,nlin2)
Q_ERRT
end if
smod0=jj
end if
else if(styp.eq.dekm%sbmb_sk)then
ier=0
if(mflag(mflaty%nsubm).eq.0)then
ier=1
else if(sekta(0).eq.nap)then
ier=1
end if
if(styp0(mz0).ne.dekm%sbmb_stm)then
if(styp0(mz0).ne.dekm%sbmb_sk)then
ier=1
end if
end if
if(smdef0.lt.0)then
smdef0=sstyp
stib(sekta(0)+1:sekta(0)+nsekt)=sstyp
if(stapi(3).eq.0)then
smdef1=1
end if
else
if(smdef0.ne.sstyp)then
ier=1
else if(stapi(3).eq.0)then
ier=1
else if(smdef1.ne.0)then
ier=1
end if
end if
if(ier.ne.0)then
go to 110
end if
q0=p0+6
do i1=1,stapi(3)
q0=q0+6
j1=stjb(q0)
j2=stjb(q0+1)
call qkbp(stcb,j1,j2,mllty%msk,j3,j4,jj)
Q_ERRT
if((jj.lt.1).or.&
(jj.gt.qll(mllty%msk)%n))then
qerrt(0)=qerrty%inp
call qmfmsg(18,nlin1,nlin2)
Q_ERRT
end if
if(stib(sekta(0)+jj).ne.sstyp)then
qerrt(0)=qerrty%inp
call qmfmsg(20,nlin1,nlin2)
Q_ERRT
end if
stib(sekta(0)+jj)=1-sstyp
end do
if(smod0.eq.tsm)then
do i1=1,nsekt
if(stib(sekta(0)+i1).eq.1)then
stib(sekts(0)+i1)=1
end if
end do
else
do i1=1,nsekt
if(stib(sekta(0)+i1).eq.1)then
if(stib(sekts(0)+i1).eq.0)then
stib(sekts(0)+i1)=-1
end if
end if
end do
end if
else if(msc(styp).eq.2)then
if(stapi(3).lt.1)then
go to 110
end if
q1=abs(sstyp)
ier=0
if(q1.lt.1)then
ier=1
else if(q1.gt.mll0)then
ier=1
else if(qll(q1)%kl.ne.qllkla%klcf)then
ier=1
end if
if(ier.ne.0)then
qerrmsg(1:srec)='qsmodel_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(sstyp.lt.0)then
q0=p0+9
j5=strty%z
else
q0=p0+6
j5=0
end if
qllp=>qll(q1)
if(qllp%n.eq.0)then
qllp%p1=stibs(1)+1
call qaoib(2)
Q_ERRT
stib(stibs(1))=eoa
qllp%p2=qllp%p1
stib(qllp%p2)=eoa
qllp%dcs=1
end if
do i1=1,stapi(3)
q0=q0+6
j1=stjb(q0)
j2=stjb(q0+1)
call qkbp(stcb,j1,j2,-qllkla%klcf,j3,j4,jj)
Q_ERRT
if(jj.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,nlin1,nlin2)
Q_ERRT
end if
if(q1.ne.mllty%mff)then
ii=llof(0)+llof(1)
else
ii=llof(0)+llof(1)+llof(3)
end if
j3=stibs(1)+1
call qaoib(ii)
Q_ERRT
stib(qllp%p2)=j3
qllp%p2=j3
stib(j3)=eoa
stib(j3+1)=j1
stib(j3+2)=j2-(j1-1)
stib(j3+3)=j5
stib(j3+llof(1):stibs(1)-1)=nap
stib(stibs(1))=eoa
qllp%n=(qllp%n)+1
end do
else if(msc(styp).eq.3)then
q1=mllty%mc
qllp=>qll(q1)
if(qllp%n.eq.0)then
if(qxmod.ne.qmod%fcon)then
qerrt(0)=qerrty%inp
call qiomsg(14,nlin1,nlin2,ifile)
Q_ERRT
end if
qllp%p1=stibs(1)+1
call qaoib(2)
Q_ERRT
stib(stibs(1))=eoa
qllp%p2=qllp%p1
stib(qllp%p2)=eoa
end if
q0=p0+6
j1=stjb(q0)
j2=stjb(q0+1)
call qkbp(stcb,j1,j2,-qllkla%klcf,j3,j4,jj)
Q_ERRT
if(jflag(jflaty%mflang).eq.0)then
if(styp.ne.dekm%c_gdef)then
go to 110
else if(jj.ne.0)then
go to 110
end if
j4=stibs(1)+1
ii=llof(0)+llof(1)
call qaoib(ii)
Q_ERRT
stib(qllp%p2)=j4
stib(j4)=eoa
stib(j4+1)=j1
stib(j4+2)=j2-(j1-1)
stib(j4+3)=0
stib(j4+llof(1):stibs(1)-1)=nap
stib(stibs(1))=eoa
qllp%p2=j4
qllp%n=(qllp%n)+1
else
if(qllp%dcs.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(14,nlin1,nlin2)
Q_ERRT
else if(j4.eq.nap)then
go to 110
else if(jj.lt.1)then
go to 110
else if(j3.ne.q1)then
go to 110
end if
if(smod0.eq.0)then
if(stib(j4+llof(2)).ne.nap)then
go to 110
end if
end if
if(smodc(0).ne.nap)then
if(stib(smodc(0)+jj).ne.0)then
go to 110
end if
stib(smodc(0)+jj)=-1
end if
end if
q0=q0+6
j5=stjb(q0)
j6=stjb(q0+1)
if(stib(j4+3).eq.strty%z)then
if(iachar(stcb(j5:j5)).eq.asq)then
j5=j5+1
j6=j6-1
end if
ii=1
if(j5.gt.j6)then
ii=0
else
ii=qstdz(stcb,j5,j6,inty%s)
Q_ERRT
end if
if(ii.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(17,nlin1,nlin2)
Q_ERRT
end if
end if
if((smod0.eq.0).or.&
(smod0.eq.tsm))then
j3=j4+llof(1)
if(stib(j3).ne.nap)then
go to 110
end if
stib(j3)=j5
stib(j3+1)=j6
go to 73
end if
else if(msc(styp).eq.4)then
if(sstyp.ne.0)then
qerrmsg(1:srec)='qsmodel_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
q0=p0+9
j1=stjb(q0)
j2=stjb(q0+1)
call qkbp(stcb,j1,j2,-qllkla%klcf,q1,j4,jj)
Q_ERRT
if(jj.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(15,nlin1,nlin2)
Q_ERRT
end if
if(sekt0.ne.0)then
if(sekty0.eq.mllty%mpf)then
if(q1.eq.mllty%mvf)then
ier=1
end if
else if(sekty0.eq.mllty%mvf)then
if(q1.ne.mllty%mvf)then
ier=1
end if
else
ier=1
end if
end if
if(ier.ne.0)then
go to 110
end if
if(qll(q1)%dcs.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(14,nlin1,nlin2)
Q_ERRT
end if
if(q1.eq.mllty%mc)then
ier=0
if(mflag(mflaty%nsubm).eq.0)then
ier=1
else if(stapi(4).ne.0)then
ier=1
end if
if(stib(j4+llof(1)).ne.nap)then
ier=1
else if(stib(j4+llof(2)).ne.nap)then
ier=1
end if
if(ier.ne.0)then
go to 110
end if
j5=j4+llof(2)
j7=q0+6
stib(j5)=stjb(j7)
stib(j5+1)=stjb(j7+1)
if(stib(j4+3).eq.strty%z)then
j1=stib(j5)
j2=stib(j5+1)
if(iachar(stcb(j1:j1)).eq.asq)then
j1=j1+1
j2=j2-1
end if
ii=1
if(j1.gt.j2)then
ii=0
else
ii=qstdz(stcb,j1,j2,inty%s)
Q_ERRT
end if
if(ii.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(17,nlin1,nlin2)
Q_ERRT
end if
end if
go to 70
end if
ier=0
q0=q0+5
if(q1.ne.mllty%mff)then
if(stjb(q0).eq.strty%p)then
ier=1
end if
else
if(stjb(q0).ne.strty%p)then
ier=1
end if
end if
if(ier.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(13,nlin1,nlin2)
Q_ERRT
end if
j7=q0+1
if(q1.ne.mllty%mff)then
if(sekt0.eq.0)then
j5=j4+llof(2)
else
j5=j4+llof(1)
end if
if(stib(j5).ne.nap)then
go to 110
end if
stib(j5)=stjb(j7)
stib(j5+1)=stjb(j7+1)
if(stib(j4+3).eq.strty%z)then
j1=stib(j5)
j2=stib(j5+1)
if(iachar(stcb(j1:j1)).eq.asq)then
j1=j1+1
j2=j2-1
end if
ii=1
if(j1.gt.j2)then
ii=0
else
ii=qstdz(stcb,j1,j2,inty%s)
Q_ERRT
end if
if(ii.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(17,nlin1,nlin2)
Q_ERRT
end if
end if
else
do i2=1,size(ffj,dim=2),2
j6=ffj(stapi(4),i2)
if(j6.gt.0)then
j5=j4+j6
if(sekt0.eq.0)then
if(i2.eq.1)then
j5=j5+2
else
j5=j5+4
end if
end if
if(stib(j5).ne.nap)then
go to 110
end if
j7=j7+ffj(stapi(4),i2+1)
stib(j5)=stjb(j7)
stib(j5+1)=stjb(j7+1)
if(stib(j4+3).eq.strty%z)then
j1=stib(j5)
j2=stib(j5+1)
if(iachar(stcb(j1:j1)).eq.asq)then
j1=j1+1
j2=j2-1
end if
ii=1
if(j1.gt.j2)then
ii=0
else
ii=qstdz(stcb,j1,j2,inty%s)
Q_ERRT
end if
if(ii.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(17,nlin1,nlin2)
Q_ERRT
end if
end if
end if
end do
end if
else if(msc(styp).eq.5)then
ier=0
if(sekt0.ne.0)then
if(sekty0.eq.mllty%mpf)then
if(styp.eq.dekm%v_def)then
ier=1
else if(sstyp.eq.mllty%mvf)then
ier=1
end if
else if(sekty0.eq.mllty%mvf)then
if(styp.eq.dekm%p_def)then
ier=1
else if(sstyp.eq.mllty%mpf)then
ier=1
end if
end if
else if(styp.eq.dekm%p_def)then
mflag(mflaty%pninskt)=1
else if(styp.eq.dekm%v_def)then
mflag(mflaty%vninskt)=1
end if
if(styp.eq.dekm%p_def)then
if(sekty1.eq.mllty%mvf)then
ier=1
end if
sekty1=mllty%mpf
else if(styp.eq.dekm%v_def)then
sekty1=mllty%mvf
end if
if(ier.ne.0)then
go to 110
end if
if(sekt0.gt.0)then
if(stib(sekts(0)+sekt0).le.0)then
go to 70
end if
end if
if(stapi(4).gt.0)then
if(jflag(jflaty%mflang).ne.0)then
sp1=(p0-1)+6*(stapi(3)+1)
sp2=(p0-7)+3*stjb(p0+1)
do i3=sp1,sp2,3
if(stjb(i3).eq.strty%p)then
if(stjb(i3+1).eq.aeq)then
j1=0
j3=i3-1
j4=stjb(j3)
j3=stjb(j3-1)
if(styp.eq.dekm%p_def)then
if(stjb(i3+3).ne.strty%p)then
j1=mllty%mpf
else if(stjb(i3+4).eq.alpar)then
j1=mllty%mff
end if
else if(styp.eq.dekm%v_def)then
if(stjb(i3+3).ne.strty%p)then
j1=mllty%mvf
end if
end if
if(j1.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(13,nlin1,nlin2)
Q_ERRT
end if
call qkbp(stcb,j3,j4,j1,j5,j6,j7)
Q_ERRT
if(j7.lt.1)then
call qkbp(stcb,j3,j4,-qllkla%klcf,j5,j6,j7)
Q_ERRT
qerrt(0)=qerrty%inp
if(j7.lt.1)then
call qmfmsg(15,nlin1,nlin2)
Q_ERRT
else
call qmfmsg(2,nlin1,nlin2)
Q_ERRT
end if
end if
end if
end if
end do
else if(qxmod.ne.qmod%fcon)then
if(styp.eq.dekm%p_def)then
if((qll(mllty%mff)%n)+(qll(mllty%mpf)%n).eq.0)then
qerrt(0)=qerrty%inp
call qiomsg(14,nlin1,nlin2,ifile)
Q_ERRT
end if
else if(styp.eq.dekm%v_def)then
if(qll(mllty%mvf)%n.eq.0)then
qerrt(0)=qerrty%inp
call qiomsg(14,nlin1,nlin2,ifile)
Q_ERRT
end if
end if
end if
end if
if(stapi(4).eq.0)then
ic1=ascol
else
ic1=acomma
end if
do i1=1,mll0
qllp=>qll(i1)
if(qllp%n.eq.0)then
cycle
else if(i1.eq.mllty%mff)then
if(styp.ne.dekm%p_def)then
cycle
end if
else if(i1.eq.mllty%mpf)then
if(styp.ne.dekm%p_def)then
cycle
end if
else if(i1.eq.mllty%mvf)then
if(styp.ne.dekm%v_def)then
cycle
end if
else
cycle
end if
j1=qllp%p1
sp1=(p0-1)+6*(stapi(3)+1)
sp2=(p0-7)+3*stjb(p0+1)
if(stjb(sp2+3).eq.strty%p)then
if(stjb(sp2+4).eq.ascol)then
if(stjb(sp2+6).eq.strty%p)then
if(stjb(sp2+7).eq.arsbr)then
j7=stjb(sp2+5)
stcb(j7:j7)=achar(aspc)
do i2=sp2+4,stjbs-3
stjb(i2)=stjb(i2+3)
end do
stjb(p0-1)=stjb(p0-1)-3
stjb(p0+1)=stjb(p0+1)-1
stjbs=stjbs-3
end if
end if
end if
end if
d02: do i2=1,qllp%n
j1=stib(j1)
j7=j1+1
j5=stib(j7)
j7=stib(j7+1)-1
j6=j5+j7
do i3=sp1,sp2,3
if(stjb(i3).eq.strty%p)then
if(stjb(i3+1).eq.aeq)then
j3=i3-1
j4=stjb(j3)
j3=stjb(j3-1)
if(j7.eq.j4-j3)then
if(stcb(j5:j6).eq.stcb(j3:j4))then
cycle d02
end if
end if
end if
end if
end do
if(i1.ne.mllty%mff)then
if(stib(j1+llof(1)).ne.nap)then
q1=j1+llof(1)
else if(stib(j1+llof(2)).ne.nap)then
q1=j1+llof(2)
else
qerrt(0)=qerrty%inp
call qmfmsg(16,nlin1,nlin2)
Q_ERRT
end if
j7=(j6-j5)+(stib(q1+1)-stib(q1))+6
call qaocb(j7)
Q_ERRT
stcb(jxb-1:jxb+j7)=achar(ic1)//' '//stcb(j5:j6)//'='//stcb(stib(q1):stib(q1+1))//' ]'//achar(alf)
jxb=jxb+j7
slin=slin+j7
else
j7=0
q1=p0+6
q2=q1+6
if(stjb(q2+1)-stjb(q2).eq.stjb(q1+1)-stjb(q1))then
if(stcb(stjb(q1):stjb(q1+1)).eq.stcb(stjb(q2):stjb(q2+1)))then
j7=1
end if
end if
if(j7.ne.0)then
if(stib(j1+llof(1)).ne.nap)then
q1=j1+llof(1)
else if(stib(j1+llof(2)).ne.nap)then
q1=j1+llof(2)
else
qerrt(0)=qerrty%inp
call qmfmsg(16,nlin1,nlin2)
Q_ERRT
end if
j7=(j6-j5)+(stib(q1+1)-stib(q1))+8
call qaocb(j7)
Q_ERRT
stcb(jxb-1:jxb+j7)=achar(ic1)//' '//stcb(j5:j6)//'=('//stcb(stib(q1):stib(q1+1))//') ]'//achar(alf)
jxb=jxb+j7
slin=slin+j7
else
if(stib(j1+llof(3)).ne.nap)then
q1=j1+llof(3)
else if(stib(j1+llof(4)).ne.nap)then
q1=j1+llof(4)
else
qerrt(0)=qerrty%inp
call qmfmsg(16,nlin1,nlin2)
Q_ERRT
end if
if(stib(q1+2).eq.nap)then
qerrt(0)=qerrty%inp
call qmfmsg(16,nlin1,nlin2)
Q_ERRT
end if
j7=(j6-j5)+(stib(q1+1)-stib(q1))+(stib(q1+3)-stib(q1+2))+10
call qaocb(j7)
Q_ERRT
stcb(jxb-1:jxb+j7)=achar(ic1)//' '//stcb(j5:j6)//'=('//stcb(stib(q1):stib(q1+1))//','//&
stcb(stib(q1+2):stib(q1+3))//') ]'//achar(alf)
jxb=jxb+j7
slin=slin+j7
end if
end if
ic1=acomma
end do d02
end do
go to 73
end if
go to 70
110 continue
qerrt(0)=qerrty%inp
call qmfmsg(2,nlin1,nlin2)
Q_ERRT
700 continue
if(mflag(mflaty%nsubm).eq.0)then
qllp=>qll(mllty%mc)
j1=qllp%p1
do i1=1,qllp%n
j1=stib(j1)
if(stib(j1+llof(1)).eq.nap)then
if(stib(j1+llof(2)).eq.nap)then
qerrt(0)=qerrty%inp
call qmfmsg(26,0,0)
Q_ERRT
end if
end if
end do
end if
if(smod0.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(24,sl1,nlin2)
Q_ERRT
end if
if(tsm.eq.0)then
if(cflag(confi%subm).ne.0)then
if(qxmod.ne.qmod%fcon)then
qerrt(0)=qerrty%inp
call qcfmsg(12,0,0)
Q_ERRT
end if
end if
end if
qllp=>qll(mllty%msm)
if(qllp%n.gt.0)then
j3=qllp%p1
do i1=1,qllp%n
j3=stib(j3)
if(stib(j3+3).eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(25,0,0)
Q_ERRT
end if
end do
end if
if(sekt0.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(19,sl1,nlin2)
Q_ERRT
end if
if(mflag(mflaty%nsubm).ne.0)then
do i1=1,nsekt
if(stib(sektb(0)+i1).eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(19,0,0)
Q_ERRT
else if(stib(sekts(0)+i1).eq.0)then
qerrt(0)=qerrty%ale
call qmfmsg(21,0,0)
Q_ERRT
end if
end do
end if
mflag(mflaty%tskt)=nsekt
qllp=>qll(mllty%msk)
j4=qllp%p1
do i1=1,nsekt
j4=stib(j4)
if(stib(sekts(0)+i1).gt.0)then
j3=stib(j4+3)
if(j3.eq.mllty%mpf)then
mflag(mflaty%npskt)=mflag(mflaty%npskt)+1
else if(j3.eq.mllty%mvf)then
mflag(mflaty%nvskt)=mflag(mflaty%nvskt)+1
else
qerrmsg(1:srec)='qsmodel_5'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
end do
73 continue
if(njb.lt.nstjb)then
call qaojb(-1)
Q_ERRT
end if
if(nstjb.ne.njb)then
qerrmsg(1:srec)='qsmodel_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(slin.gt.0)then
slin=jxb-jxa
end if
99 continue
return
end subroutine qsmodel
subroutine qmodel
use,non_intrinsic::qaski
use,non_intrinsic::qbounds,only:maxphi0,maxvertx0
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstdq,qstds,qstdw,qstdz,qstoz
integer(kind=c_int_least32_t)::ii,ij,i1,i2,id1,id2,idin,is1,is2,ix,jj,j1,j2
integer(kind=c_int_least32_t)::ixa,ixb,ifile,njb
integer(kind=c_int_least32_t)::dbl,fpass,ibot,ic,itop,kid,kin,kk,knf
integer(kind=c_int_least32_t)::level,mpal,nest,quote,slin,vel,vin
integer(kind=c_int_least32_t)::newid,nlin,off1,off2,pal,plm,psize
integer(kind=c_int_least32_t)::llk(1:3),llkt(1:3),llp(2:3),llpt(2:3)
integer(kind=c_int_least32_t)::apmkd(0:0),avmkd(0:0)
integer(kind=c_int_least32_t)::sucpal(0:11,0:11),acf0(0:127)
njb=nstjb
acf0(0:31)=-1
acf0(32:126)=0
acf0(127)=-1
acf0(alf)=1
acf0(aspc)=2
acf0(adq)=3
acf0(asq)=4
acf0(iachar('('))=5
acf0(iachar(')'))=6
acf0(iachar(','))=7
acf0(iachar(';'))=8
acf0(aeq)=9
acf0(iachar('['))=10
acf0(iachar(']'))=11
sucpal(:,:)=-1
sucpal(0,2)=0
sucpal(0,10)=1
sucpal(1,0)=1
sucpal(1,1)=1
sucpal(1,2)=1
sucpal(1,7)=1
sucpal(1,8)=2
sucpal(1,9)=3
sucpal(1,11)=10
sucpal(2,0)=2
sucpal(2,1)=2
sucpal(2,2)=2
sucpal(2,9)=3
sucpal(3,0)=3
sucpal(3,1)=3
sucpal(3,2)=3
sucpal(3,3)=-1
sucpal(3,4)=5
sucpal(3,5)=6
sucpal(3,7)=2
sucpal(3,11)=10
sucpal(4,0)=4
sucpal(4,2)=4
sucpal(4,3)=3
sucpal(4,4)=4
sucpal(4,5)=4
sucpal(4,6)=4
sucpal(4,7)=4
sucpal(4,8)=4
sucpal(4,9)=4
sucpal(4,10)=4
sucpal(4,11)=4
sucpal(5,0)=5
sucpal(5,2)=5
sucpal(5,3)=5
sucpal(5,4)=3
sucpal(5,5)=5
sucpal(5,6)=5
sucpal(5,7)=5
sucpal(5,8)=5
sucpal(5,9)=5
sucpal(5,10)=5
sucpal(5,11)=5
sucpal(6,0)=6
sucpal(6,1)=6
sucpal(6,2)=6
sucpal(6,3)=-1
sucpal(6,4)=8
sucpal(6,6)=9
sucpal(6,7)=6
sucpal(7,0)=7
sucpal(7,2)=7
sucpal(7,3)=6
sucpal(7,4)=7
sucpal(7,5)=7
sucpal(7,6)=7
sucpal(7,7)=7
sucpal(7,8)=7
sucpal(7,9)=7
sucpal(7,10)=7
sucpal(7,11)=7
sucpal(8,0)=8
sucpal(8,2)=8
sucpal(8,3)=8
sucpal(8,4)=6
sucpal(8,5)=8
sucpal(8,6)=8
sucpal(8,7)=8
sucpal(8,8)=8
sucpal(8,9)=8
sucpal(8,10)=8
sucpal(8,11)=8
sucpal(9,1)=9
sucpal(9,2)=9
sucpal(9,7)=2
sucpal(9,11)=10
sucpal(10,1)=11
ifile=0
do i1=nfiles,1,-1
if(filt(i1).eq.qfty%mtyp)then
ifile=i1
exit
end if
end do
nlin=0
dbl=0
level=1
if(filt(i1).eq.qfty%mtyp)then
llk(:)=nap
llkt(:)=nap
llp(:)=nap
llpt(:)=nap
mrho=maxdeg
nrho=0
end if
70 continue
if(njb.lt.nstjb)then
call qaojb(-1)
Q_ERRT
end if
call qsmodel(dbl,nlin,slin,ixa,ixb)
Q_ERRT
if(slin.eq.0)then
go to 521
else if(slin.lt.0)then
go to 777
end if
ibot=ixa
itop=ixa+(slin-1)
do i1=ibot,itop
if(iachar(stcb(i1:i1)).ne.aspc)then
ibot=i1
exit
end if
end do
ii=0
nest=0
quote=0
do i1=ibot,itop
jj=iachar(stcb(i1:i1))
if(jj.eq.asq)then
if(nest.ne.1)then
go to 521
end if
if(quote.eq.0)then
quote=asq
end if
if(quote.eq.asq)then
ii=1-ii
end if
else if(jj.eq.adq)then
if(nest.ne.1)then
go to 521
end if
if(quote.eq.0)then
quote=adq
end if
if(quote.eq.adq)then
ii=1-ii
end if
else if(ii.eq.0)then
if(stcb(i1:i1).eq.'[')then
if(nest.ne.0)then
go to 521
end if
nest=1
else if(stcb(i1:i1).eq.']')then
if(nest.ne.1)then
go to 521
end if
nest=2
else if(stcb(i1:i1).eq.',')then
if(nest.ne.1)then
go to 521
end if
quote=0
else if(jj.ne.aspc)then
if(nest.ne.1)then
go to 521
end if
end if
else
if(nest.ne.1)then
go to 521
end if
end if
end do
if(ii.ne.0)then
go to 521
end if
if(stcb(itop:itop).ne.']')then
go to 521
end if
if(nest.ne.2)then
go to 521
end if
50 continue
pal=0
mpal=11
vel=0
vin=0
idin=0
kin=0
kid=0
knf=0
id1=0
id2=0
is1=0
is2=0
plm=0
itop=ixb
ix=ibot
280 continue
ic=iachar(stcb(ix:ix))
if(sucpal(pal,acf0(ic)).lt.0)then
go to 521
end if
if(pal.lt.3)then
if(pal.eq.1)then
if(acf0(ic).eq.0)then
if(id1.eq.0)then
id1=ix
end if
id2=ix
else if(acf0(ic).gt.2)then
if(stcb(ix:ix).eq.',')then
if(level.eq.1)then
if(ngmk.gt.0)then
call qrgmki(llk(1),llkt(1))
Q_ERRT
end if
level=2
fpass=1
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
off1=0
end if
else if(stcb(ix:ix).eq.';')then
if(level.lt.2)then
go to 521
end if
else if(stcb(ix:ix).eq.'=')then
if((level.ne.1).or.&
(kin.ne.0))then
go to 521
end if
kin=1
go to 283
else if(stcb(ix:ix).eq.']')then
if(level.lt.2)then
go to 521
end if
end if
if(level.eq.2)then
idin=idin+1
if(idin.gt.5)then
go to 521
end if
go to 281
else if(level.eq.3)then
idin=idin+1
go to 282
end if
end if
else if(pal.eq.2)then
if(stcb(ix:ix).eq.'=')then
kin=kin+1
go to 283
else if(acf0(ic).eq.0)then
if(id1.eq.0)then
id1=ix
end if
id2=ix
end if
end if
else if(pal.lt.6)then
if(pal.eq.3)then
if((vel.ne.0).or.&
(vin.ne.0))then
go to 521
end if
if(iachar(stcb(ix:ix)).eq.asq)then
plm=1-plm
if(is1.eq.0)then
is1=ix
end if
is2=ix
else
if(acf0(ic).eq.0)then
if(is1.eq.0)then
is1=ix
end if
is2=ix
else if(stcb(ix:ix).eq.'(')then
if(is1.ne.0)then
go to 521
end if
vel=1
else if((stcb(ix:ix).eq.',').or.&
(stcb(ix:ix).eq.']'))then
go to 285
end if
end if
else if(pal.eq.4)then
else if(pal.eq.5)then
if((vel.ne.0).or.&
(vin.ne.0).or.&
(plm.ne.1))then
go to 521
end if
if(iachar(stcb(ix:ix)).eq.asq)then
plm=1-plm
end if
is2=ix
end if
else if(pal.lt.9)then
if(pal.eq.6)then
if((vel.ne.1).or.&
(plm.ne.0))then
go to 521
end if
if(iachar(stcb(ix:ix)).eq.asq)then
plm=1-plm
if(is1.eq.0)then
is1=ix
end if
is2=ix
else
if(acf0(ic).eq.0)then
if(is1.eq.0)then
is1=ix
end if
is2=ix
else if((stcb(ix:ix).eq.',').or.&
(stcb(ix:ix).eq.')'))then
vin=vin+1
go to 285
end if
end if
else if(pal.eq.7)then
else if(pal.eq.8)then
if((vel.ne.1).or.&
(plm.ne.1))then
go to 521
end if
if(iachar(stcb(ix:ix)).eq.asq)then
plm=1-plm
end if
is2=ix
end if
else if(pal.lt.12)then
if(pal.eq.9)then
if((level.gt.2).or.&
(level.le.0))then
go to 521
end if
if((stcb(ix:ix).eq.',').or.&
(stcb(ix:ix).eq.']'))then
vin=0
vel=0
end if
else if(pal.eq.10)then
else if(pal.eq.11)then
end if
else
go to 521
end if
287 continue
pal=sucpal(pal,acf0(ic))
if(ix.lt.itop)then
ix=ix+1
go to 280
end if
if(vel.ne.0)then
go to 521
else if(pal.ne.mpal)then
go to 521
else if(plm.ne.0)then
go to 521
else if(id1.ne.0)then
go to 521
else if(is1.ne.0)then
go to 521
end if
if(level.eq.1)then
go to 70
else if(level.eq.2)then
if(fpass.eq.0)then
do i1=1,npmk
if(stib(apmkd(0)+i1).eq.3)then
if(stib(llpt(2)+1).eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(13,dbl,nlin)
Q_ERRT
end if
end if
if(stib(apmkd(0)+i1).ne.stib(pmkd(0)+i1))then
ii=1
if(stib(apmkd(0)+i1).eq.2)then
if(stib(pmkd(0)+i1).eq.3)then
ii=stib(llpt(2)+1)
end if
end if
if(ii.ne.0)then
if(stib(apmkd(0)+i1).eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(16,dbl,nlin)
Q_ERRT
else
qerrt(0)=qerrty%inp
call qmfmsg(13,dbl,nlin)
Q_ERRT
end if
end if
end if
end do
nprop=nprop+1
end if
else if(level.eq.3)then
if(fpass.eq.0)then
do i1=1,nvmk
if(stib(avmkd(0)+i1).eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(16,dbl,nlin)
Q_ERRT
end if
end do
jj=stib(llpt(3)+1)
if(jj.lt.3)then
qerrt(0)=qerrty%inp
call qmfmsg(9,dbl,nlin)
Q_ERRT
end if
ii=0
do i1=1,jj
if(stib(antiq(0)+stib(llpt(3)+1+i1)).ne.0)then
ii=1-ii
end if
end do
if(ii.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(11,dbl,nlin)
Q_ERRT
end if
end if
end if
if(level.eq.2)then
if(fpass.ne.0)then
ii=stibs(1)+1
call qaoib(4)
Q_ERRT
stib(ii:stibs(1))=eoa
ii=npmk+1
call qtrm(4,ii,stibs(1))
Q_ERRT
pmkd(0)=stibs(1)-ii
pmkl(0)=pmkd(0)-ii
pmkp(0)=pmkl(0)-ii
if(npmk.gt.0)then
jj=pmkp(0)-llk(2)+1
call qxipht(pmkp(0)+1,stibs(1),-jj)
Q_ERRT
call qaoib(-jj)
Q_ERRT
pmkd(0)=pmkd(0)-jj
pmkl(0)=pmkl(0)-jj
pmkp(0)=pmkp(0)-jj
end if
apmkd(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
psize=7+2*npmk
end if
if(npmk.gt.0)then
stib(apmkd(0)+1:apmkd(0)+npmk)=0
end if
if(fpass.ne.0)then
fpass=0
if(idin.lt.3)then
go to 521
end if
go to 50
end if
else if(level.eq.3)then
if(fpass.ne.0)then
ii=stibs(1)+1
call qaoib(3)
Q_ERRT
stib(ii:stibs(1))=eoa
ii=nvmk+1
call qtrm(3,ii,stibs(1))
Q_ERRT
vmkl(0)=stibs(1)-ii
vmkp(0)=vmkl(0)-ii
avmkd(0)=vmkp(0)-ii
call qxipht(vmkp(0),stibs(1),-1)
Q_ERRT
call qaoib(-1)
Q_ERRT
vmkl(0)=vmkl(0)-1
vmkp(0)=vmkp(0)-1
avmkd(0)=avmkd(0)-1
else
if(nvert.eq.maxvertx0)then
qerrt(0)=qerrty%inp
call qmfmsg(29,dbl,nlin)
Q_ERRT
end if
nvert=nvert+1
end if
if(nvmk.gt.0)then
stib(avmkd(0)+1:avmkd(0)+nvmk)=0
end if
if(fpass.ne.0)then
fpass=0
go to 50
end if
end if
go to 70
281 continue
if(idin.eq.3)then
j2=qstdw(stcb,id1,id2)
Q_ERRT
if(j2.ne.0)then
if(knf.ne.2)then
qerrt(0)=qerrty%inp
call qmfmsg(4,dbl,nlin)
Q_ERRT
end if
knf=0
if(nphi.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(6,0,0)
Q_ERRT
end if
call qrpi(llp(2),llpt(2))
Q_ERRT
level=3
fpass=1
go to 50
end if
ii=iachar(stcb(id1:id1))
if(ii.ne.aplus)then
if(ii.ne.aminus)then
go to 521
end if
end if
if(id1.eq.id2)then
if(cflag(confi%qn).eq.0)then
cflag(confi%qn)=1
else if(cflag(confi%qn).ne.1)then
go to 521
end if
jj=0
else if(id1.eq.id2-1)then
ii=iachar(stcb(id2:id2))
if(int(ii-1).ne.azero)then
go to 521
end if
if(cflag(confi%qn).eq.0)then
cflag(confi%qn)=2
else if(cflag(confi%qn).ne.2)then
go to 521
end if
else
go to 521
end if
if(knf.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(5,dbl,nlin)
Q_ERRT
end if
if(fpass.eq.0)then
ii=iachar(stcb(id1:id1))
if(ii.eq.aplus)then
stib(off1+3)=0
else if(ii.eq.aminus)then
stib(off1+3)=1
else
go to 521
end if
stib(off1+4)=phity%dflt
if(off2.ne.0)then
stib(off2+3)=stib(off1+3)
stib(off2+4)=stib(off1+4)
end if
stib(llpt(2))=off1+1
stib(off1+1)=eoa
llpt(2)=off1+1
if(off2.ne.0)then
stib(llpt(2))=off2+1
stib(off2+1)=eoa
llpt(2)=off2+1
end if
end if
go to 284
else if(idin.gt.3)then
if(fpass.eq.0)then
ij=0
call qmstr0(stcb,id1,id2,popt6(0),wopt6(0),aopt6(0),ij)
Q_ERRT
if(ij.eq.0)then
go to 521
end if
ij=stib(copt6(0)+ij)
if(idin.eq.4)then
stib(off1+4)=ij
else if(idin.eq.5)then
if((ij.eq.phity%int).and.&
(stib(off1+4).eq.phity%notdp))then
stib(off1+4)=phity%ntint
else if((ij.eq.phity%notdp).and.&
(stib(off1+4).eq.phity%int))then
stib(off1+4)=phity%ntint
else
go to 521
end if
else
go to 521
end if
if(off2.ne.0)then
stib(off2+4)=stib(off1+4)
end if
end if
go to 284
end if
if(id1.le.0)then
go to 521
else if(id1.gt.id2)then
go to 521
else
j2=qstdw(stcb,id1,id2)
Q_ERRT
if(j2.eq.0)then
qerrmsg(1:srec)="unacceptable field name,"//achar(anull)
qerrt(0)=qerrty%inp
call qmput(dbl,nlin,ifile)
Q_ERRT
end if
end if
if(fpass.ne.0)then
go to 284
end if
kk=id2-id1+1
if(kk.le.0)then
go to 521
end if
newid=1
if(nphi.gt.0)then
call qmstr1(stcb,id1,id2,llp(2),4,5,ij,ii)
Q_ERRT
if(ij.ne.0)then
newid=0
end if
end if
if(newid.eq.0)then
if(idin.eq.1)then
knf=1
else if(idin.eq.2)then
if(knf.eq.1)then
knf=2
else if(ij.ne.nphi)then
knf=1
end if
end if
end if
if(knf.ne.0)then
go to 284
end if
if(idin.eq.1)then
if(nprop.eq.0)then
call qaoib(2)
Q_ERRT
stib(stibs(1)-1)=eoa
stib(stibs(1))=eoa
llp(2)=stibs(1)-1
llpt(2)=llp(2)
end if
off1=stibs(1)
off2=0
call qaoib(psize)
Q_ERRT
stib(off1+2:stibs(1)-1)=0
stib(stibs(1))=eoa
stib(off1+5)=id1
stib(off1+6)=id2-id1+1
else if(idin.eq.2)then
newid=1
i1=stib(off1+5)
i2=stib(off1+6)
if(id2-id1+1.eq.i2)then
if(stcb(id1:id2).eq.stcb(i1:i1-1+i2))then
newid=0
end if
end if
if(newid.eq.0)then
stib(off1+2)=0
go to 284
end if
off2=stibs(1)
call qaoib(psize)
Q_ERRT
stib(off2+2:stibs(1)-1)=0
stib(stibs(1))=eoa
stib(off2+5)=id1
stib(off2+6)=id2-id1+1
stib(off1+2)=1
stib(off2+2)=-1
else
qerrmsg(1:srec)='qmodel_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(nphi.eq.maxphi0)then
qerrt(0)=qerrty%inp
call qmfmsg(30,dbl,nlin)
Q_ERRT
end if
nphi=nphi+1
284 continue
id1=0
go to 287
282 continue
if(id1.le.0)then
go to 521
else if(id1.gt.id2)then
go to 521
else
j2=qstdw(stcb,id1,id2)
Q_ERRT
if(j2.eq.0)then
qerrmsg(1:srec)="unacceptable field name,"//achar(anull)
qerrt(0)=qerrty%inp
call qmput(dbl,nlin,ifile)
Q_ERRT
end if
end if
if(idin.gt.maxdeg)then
qerrt(0)=qerrty%inp
call qmfmsg(10,dbl,nlin)
Q_ERRT
end if
if(idin.gt.nrho)then
nrho=idin
end if
if(fpass.ne.0)then
go to 286
end if
if(idin.eq.1)then
if(nvert.eq.0)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
llp(3)=stibs(1)
llpt(3)=llp(3)
end if
ii=stibs(1)+1
jj=2+2*nvmk
call qaoib(jj)
Q_ERRT
stib(llpt(3))=ii
llpt(3)=ii
stib(llpt(3))=eoa
stib(llpt(3)+1:stibs(1))=0
end if
ij=0
call qmstr0(stcb,id1,id2,namep(0),namel(0),nap,ij)
Q_ERRT
if(ij.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(4,dbl,nlin)
Q_ERRT
end if
call qaoib(1)
Q_ERRT
stib(stibs(1))=0
stib(llpt(3)+1+idin)=ij
stib(llpt(3)+1)=stib(llpt(3)+1)+1
286 continue
id1=0
go to 287
283 continue
if(id1.le.0)then
go to 521
else if(id1.gt.id2)then
go to 521
else
j2=qstdw(stcb,id1,id2)
Q_ERRT
if(j2.eq.0)then
go to 521
end if
end if
if(level.eq.1)then
if(kin.gt.1)then
go to 521
end if
if(ngmk.eq.0)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
llk(1)=stibs(1)
llkt(1)=llk(1)
else
call qmstr1(stcb,id1,id2,llk(1),1,2,ij,ii)
Q_ERRT
if(ij.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,dbl,nlin)
Q_ERRT
end if
end if
ij=0
call qmstr0(stcb,id1,id2,udkp(0),udkl(0),nap,ij)
Q_ERRT
ii=stibs(1)+1
call qaoib(4)
Q_ERRT
if(ij.eq.0)then
stib(ii+1)=id1
else
stib(ii+1)=stib(udkp(0)+ij)
end if
stib(ii+2)=id2-id1+1
stib(llkt(1))=ii
llkt(1)=ii
stib(ii)=eoa
stib(stibs(1))=eoa
ngmk=ngmk+1
else if(level.eq.2)then
if(fpass.ne.0)then
ij=0
call qmstr0(stcb,id1,id2,gmkp(0),gmkl(0),nap,ij)
Q_ERRT
if(ij.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,dbl,nlin)
Q_ERRT
end if
if(npmk.eq.0)then
call qaoib(2)
Q_ERRT
stib(stibs(1)-1)=eoa
stib(stibs(1))=eoa
llk(2)=stibs(1)-1
llkt(2)=llk(2)
else
call qmstr1(stcb,id1,id2,llk(2),1,2,ij,ii)
Q_ERRT
if(ij.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,dbl,nlin)
Q_ERRT
end if
end if
ij=0
call qmstr0(stcb,id1,id2,udkp(0),udkl(0),nap,ij)
Q_ERRT
ii=stibs(1)+1
call qaoib(4)
Q_ERRT
if(ij.eq.0)then
stib(ii+1)=id1
stib(ii+2)=id2-id1+1
else
stib(ii+1)=stib(udkp(0)+ij)
stib(ii+2)=stib(udkl(0)+ij)
end if
stib(stibs(1))=0
stib(llkt(2))=ii
llkt(2)=ii
stib(llkt(2))=eoa
npmk=npmk+1
else
kid=0
call qmstr0(stcb,id1,id2,pmkp(0),pmkl(0),nap,kid)
Q_ERRT
if(kid.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(15,dbl,nlin)
Q_ERRT
end if
if(stib(apmkd(0)+kid).ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,dbl,nlin)
Q_ERRT
end if
end if
else if(level.eq.3)then
if(fpass.ne.0)then
ij=0
call qmstr0(stcb,id1,id2,gmkp(0),gmkl(0),nap,ij)
Q_ERRT
if(ij.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,dbl,nlin)
Q_ERRT
end if
ij=0
call qmstr0(stcb,id1,id2,pmkp(0),pmkl(0),nap,ij)
Q_ERRT
if(ij.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,dbl,nlin)
Q_ERRT
end if
if(nvmk.eq.0)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
llk(3)=stibs(1)
llkt(3)=llk(3)
else
call qmstr1(stcb,id1,id2,llk(3),1,2,ij,ii)
Q_ERRT
if(ij.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,dbl,nlin)
Q_ERRT
end if
end if
ij=0
call qmstr0(stcb,id1,id2,udkp(0),udkl(0),nap,ij)
Q_ERRT
ii=stibs(1)+1
call qaoib(3)
Q_ERRT
if(ij.eq.0)then
stib(stibs(1)-1)=id1
stib(stibs(1))=id2-id1+1
else
stib(stibs(1)-1)=stib(udkp(0)+ij)
stib(stibs(1))=stib(udkl(0)+ij)
end if
stib(llkt(3))=ii
llkt(3)=ii
stib(llkt(3))=eoa
nvmk=nvmk+1
else
kid=0
call qmstr0(stcb,id1,id2,vmkp(0),vmkl(0),nap,kid)
Q_ERRT
if(kid.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(16,dbl,nlin)
Q_ERRT
end if
if(stib(avmkd(0)+kid).ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(12,dbl,nlin)
Q_ERRT
end if
end if
end if
id1=0
go to 287
285 continue
if(is1.eq.0)then
go to 521
else if(is1.gt.is2)then
go to 521
end if
if(level.eq.1)then
call qaoib(2)
Q_ERRT
j1=llkt(1)+3
if(vel.eq.0)then
stib(j1)=1
else
stib(j1)=vin+1
end if
if(vel.ne.0)then
qerrt(0)=qerrty%inp
call qmfmsg(13,dbl,nlin)
Q_ERRT
end if
else if(level.eq.2)then
if(fpass.ne.0)then
j1=llkt(2)+3
if(vel.eq.0)then
stib(j1)=1
else
stib(j1)=3
end if
go to 184
else
j1=apmkd(0)+kid
if(vel.eq.0)then
stib(j1)=1
else
stib(j1)=vin+1
end if
if(stib(j1).gt.stib(pmkd(0)+kid))then
qerrt(0)=qerrty%inp
call qmfmsg(13,dbl,nlin)
Q_ERRT
end if
end if
if(vin.gt.2)then
qerrt(0)=qerrty%inp
call qmfmsg(13,dbl,nlin)
Q_ERRT
end if
else if(level.eq.3)then
if(vel.ne.0)then
go to 521
end if
if(fpass.ne.0)then
go to 184
else
stib(avmkd(0)+kid)=1
end if
end if
if(iachar(stcb(is1:is1)).eq.asq)then
kk=qstds(stcb,is1,is2,1)
Q_ERRT
if(kk.lt.0)then
go to 521
else if(kk.gt.0)then
if(kk+1.lt.is2-is1)then
is1=stcbs(1)-kk
else
is1=is1+1
end if
end if
else
j1=qstdw(stcb,is1,is2)
Q_ERRT
if(j1.eq.0)then
j1=qstdq(stcb,is1,is2,inty%s)
Q_ERRT
if(j1.eq.0)then
if(qxmod.eq.qmod%fcon)then
if(stofc.gt.0)then
j1=qstdq(stcb,is1,is2,inty%l)
Q_ERRT
end if
end if
if(j1.eq.0)then
go to 521
end if
end if
end if
kk=is2-is1+1
end if
if(level.eq.1)then
stib(stibs(1)-1)=is1
stib(stibs(1))=kk
else if(level.eq.2)then
jj=6+kid
if(vel.ne.0)then
if(vin.eq.1)then
j1=off1+jj
else if(vin.eq.2)then
j1=off2+jj
end if
stib(j1)=is1
stib(j1+npmk)=kk
else
j1=off1+jj
stib(j1)=is1
stib(j1+npmk)=kk
if(off2.ne.0)then
j1=off2+jj
stib(j1)=is1
stib(j1+npmk)=kk
end if
end if
else if(level.eq.3)then
jj=llpt(3)+stib(llpt(3)+1)+2*kid
stib(jj)=is1
stib(jj+1)=kk
end if
184 continue
is1=0
go to 287
521 continue
qerrt(0)=qerrty%inp
call qmfmsg(2,dbl,nlin)
Q_ERRT
777 continue
if(nvert.eq.0)then
qerrt(0)=qerrty%inp
call qmfmsg(7,0,0)
Q_ERRT
end if
call qrvi(llp(3),llpt(3))
Q_ERRT
if(njb.lt.nstjb)then
call qaojb(-1)
Q_ERRT
end if
if(nstjb.ne.njb)then
qerrmsg(1:srec)='qmodel_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
99 continue
return
end subroutine qmodel
subroutine qrgmki(p1,p2)
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::p1,p2
integer(kind=c_int_least32_t)::ii,i1,j1,j2,j3,jj,tgmkr
if((p1.eq.nap).or.&
(p2.eq.nap))then
qerrmsg(1:srec)='qrgmki_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(ngmk.eq.0)then
gmkp(0)=nap
gmkl(0)=nap
gmkr(0)=nap
gmko(0)=nap
gmkvp(0)=nap
gmkvl(0)=nap
call qaoib(-1)
Q_ERRT
go to 99
end if
ii=ngmk+1
gmkp(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
gmkl(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
gmkr(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
gmko(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
j1=0
tgmkr=0
jj=p1
do while(stib(jj).ne.eoa)
jj=stib(jj)
j1=j1+1
stib(gmkp(0)+j1)=stib(jj+1)
stib(gmkl(0)+j1)=stib(jj+2)
stib(gmkr(0)+j1)=stib(jj+3)
stib(gmko(0)+j1)=tgmkr
tgmkr=tgmkr+max(1,stib(jj+3)-1)
end do
if(jj.ne.p2)then
qerrmsg(1:srec)='qrgmki_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=tgmkr+1
gmkvp(0)=stibs(1)
call qaoib(2*ii)
Q_ERRT
gmkvl(0)=gmkvp(0)+ii
stib(gmkvl(0))=eoa
stib(stibs(1))=eoa
j1=gmkr(0)
j2=0
jj=p1
do while(stib(jj).ne.eoa)
jj=stib(jj)
j1=j1+1
j3=jj+3
do i1=1,max(1,stib(j1)-1)
j2=j2+1
j3=j3+1
stib(gmkvp(0)+j2)=stib(j3)
j3=j3+1
stib(gmkvl(0)+j2)=stib(j3)
end do
end do
99 continue
return
end subroutine qrgmki
subroutine qrpi(p1,p2)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qproc
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::p1,p2
integer(kind=c_int_least32_t), external::qstoz,qstdfty
integer(kind=c_int_least32_t)::ii,i1,i2,ij,j1,j2,j3,j4,p0
if((p1.eq.nap).or.&
(p2.eq.nap))then
qerrmsg(1:srec)='qrpi_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=nphi+1
call qaoib(6*ii)
Q_ERRT
stib(stibs(1))=eoa
blok(0)=stibs(1)-ii
stib(blok(0))=eoa
link(0)=blok(0)-ii
stib(link(0))=eoa
antiq(0)=link(0)-ii
stib(antiq(0))=eoa
tpc(0)=antiq(0)-ii
stib(tpc(0))=eoa
namel(0)=tpc(0)-ii
stib(namel(0))=eoa
namep(0)=namel(0)-ii
if(npmk.gt.0)then
pmkvfpp(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
pmkvflp(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
else
pmkvfpp(0)=nap
pmkvflp(0)=nap
end if
j3=0
j4=p1
do while(stib(j4).ne.eoa)
j4=stib(j4)
j3=j3+1
stib(link(0)+j3)=stib(j4+1)
stib(antiq(0)+j3)=stib(j4+2)
stib(tpc(0)+j3)=stib(j4+3)
stib(namep(0)+j3)=stib(j4+4)
stib(namel(0)+j3)=stib(j4+5)
if(npmk.gt.0)then
stib(pmkvfpp(0)+j3)=j4+5
stib(pmkvflp(0)+j3)=j4+5+npmk
end if
end do
if(j4.ne.p2)then
qerrmsg(1:srec)='qrpi_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
do i1=1,nphi
j1=stib(tpc(0)+i1)
j2=stib(link(0)+i1)
stib(link(0)+i1)=j2+i1
if(j1.eq.phity%ext)then
mflag(mflaty%ext)=1
else
if((j1.eq.phity%notdp).or.&
(j1.eq.phity%ntint))then
mflag(mflaty%notadp)=1
end if
if(j2.ge.0)then
npprop=npprop+1
end if
end if
end do
if(npmk.eq.0)then
pmkt(0)=nap
pmkzp(0)=nap
pmkvmi(0)=nap
pmkvma(0)=nap
go to 99
end if
ii=npmk+1
pmkt(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
j1=pmkt(0)+1
j2=pmkt(0)+npmk
do i1=1,npmk
ij=0
do i2=1,nphi
j1=stib(stib(pmkvfpp(0)+i2)+i1)
j2=stib(stib(pmkvflp(0)+i2)+i1)
if(j2.eq.0)then
j3=futyp%sqs
else
j2=(j1-1)+j2
j3=qstdfty(stcb,j1,j2)
end if
if(i2.eq.1)then
ij=j3
else
ij=min(j3,ij)
end if
if(ij.ne.futyp%z)then
if(ij.ne.futyp%q)then
ij=futyp%sqs
exit
end if
end if
end do
stib(pmkt(0)+i1)=ij
end do
ii=npmk+1
pmkzp(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
pmkvmi(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
pmkvma(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
do i1=1,npmk
if(stib(pmkt(0)+i1).eq.futyp%z)then
p0=stibs(1)
stib(pmkzp(0)+i1)=p0
ii=nphi
call qaoib(ii)
Q_ERRT
do i2=1,nphi
j1=stib(stib(pmkvfpp(0)+i2)+i1)
j2=j1+(stib(stib(pmkvflp(0)+i2)+i1)-1)
ij=qstoz(stcb,j1,j2,inty%s)
Q_ERRT
if(i2.gt.1)then
if(ij.lt.j3)then
j3=ij
else if(ij.gt.j4)then
j4=ij
end if
else
j3=ij
j4=ij
end if
stib(p0+i2)=ij
end do
else
j3=0
j4=0
end if
stib(pmkvmi(0)+i1)=j3
stib(pmkvma(0)+i1)=j4
end do
if(stib(stibs(1)).ne.eoa)then
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
end if
99 continue
return
end subroutine qrpi
subroutine qrvi(p1,p2)
use,non_intrinsic::qcbuffer
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::p1,p2
integer(kind=c_int_least32_t), external::qsigz,qstdfty
integer(kind=c_int_least32_t)::xtmp(1:maxdeg+1),nrot(1:maxdeg),rotvpo(1:maxdeg)
integer(kind=c_int_least32_t)::hi,hj,ii,ij,jj,jk,kk
integer(kind=c_int_least32_t)::h1,h2,i1,i2,i3,i4,j1,j2,j3
if((p1.eq.nap).or.&
(p2.eq.nap))then
qerrmsg(1:srec)='qrvi_6'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
ii=nrho+1
nivd(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
ii=nvert+1
vval(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
vparto(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
jj=nvmk+1
vmkvpp(0)=stibs(1)
call qaoib(jj)
Q_ERRT
stib(stibs(1))=eoa
vmkvlp(0)=stibs(1)
call qaoib(jj)
Q_ERRT
stib(stibs(1))=eoa
j1=stibs(1)
call qaoib(2*nvmk*ii)
Q_ERRT
do i1=1,nvmk
stib(vmkvpp(0)+i1)=j1
j1=j1+ii
stib(j1)=eoa
stib(vmkvlp(0)+i1)=j1
j1=j1+ii
stib(j1)=eoa
end do
if(nrho.lt.3)then
qerrmsg(1:srec)='qrvi_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
if(nrho.gt.0)then
nrot(1:nrho)=0
stib(nivd(0)+1:nivd(0)+nrho)=0
end if
j1=0
jj=p1
do while(stib(jj).ne.eoa)
jj=stib(jj)
j1=j1+1
j2=stib(jj+1)
stib(vval(0)+j1)=j2
j2=j2+nivd(0)
stib(j2)=stib(j2)+1
end do
if((j1.ne.nvert).or.&
(jj.ne.p2))then
qerrmsg(1:srec)='qrvi_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
mrho=nrho
do i1=1,nvert
j1=stib(vval(0)+i1)
if(j1.lt.mrho)then
mrho=j1
end if
end do
j1=0
jj=p1
do while(stib(jj).ne.eoa)
jj=stib(jj)
j1=j1+1
j2=jj+stib(vval(0)+j1)
do i1=1,nvmk
j2=j2+2
stib(stib(vmkvpp(0)+i1)+j1)=stib(j2)
stib(stib(vmkvlp(0)+i1)+j1)=stib(j2+1)
end do
end do
if(j1.ne.nvert)then
qerrmsg(1:srec)='qrvi_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
kk=p1
if(p1.gt.1)then
if(stib(p1-1).eq.eoa)then
kk=p1-1
end if
end if
ij=stib(p1)
stib(p1)=eoa
j1=0
50 continue
jj=ij
if(jj.ne.eoa)then
j1=j1+1
ij=stib(ij)
j2=jj-kk+1
call qxipht(jj+2,jj+1+stib(vval(0)+j1),-j2)
Q_ERRT
stib(vparto(0)+j1)=kk
kk=kk+stib(vval(0)+j1)
go to 50
end if
if(j1.ne.nvert)then
qerrmsg(1:srec)='qrvi_5'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
kk=nivd(0)-kk-1
call qxipht(nivd(0),stibs(1),-kk)
Q_ERRT
call qaoib(-kk)
Q_ERRT
nivd(0)=nivd(0)-kk
vval(0)=vval(0)-kk
vparto(0)=vparto(0)-kk
vmkvpp(0)=vmkvpp(0)-kk
vmkvlp(0)=vmkvlp(0)-kk
do i1=1,nvmk
stib(vmkvpp(0)+i1)=stib(vmkvpp(0)+i1)-kk
stib(vmkvlp(0)+i1)=stib(vmkvlp(0)+i1)-kk
end do
stib(nivd(0))=eoa
jj=nvmk+1
vmkt(0)=stibs(1)
call qaoib(jj)
Q_ERRT
stib(stibs(1))=eoa
vmks(0)=stibs(1)
call qaoib(jj)
Q_ERRT
stib(stibs(1))=eoa
if(nvmk.gt.0)then
stib(vmks(0)+1:vmks(0)+nvmk)=0
end if
do i1=1,nvmk
ii=stib(vmkvpp(0)+i1)
jj=stib(vmkvlp(0)+i1)
ij=0
do i2=1,nvert
j1=stib(ii+i2)
j2=stib(jj+i2)
if(j2.eq.0)then
j3=futyp%sqs
else
j2=(j1-1)+j2
j3=qstdfty(stcb,j1,j2)
end if
if(i2.eq.1)then
ij=j3
else
ij=min(j3,ij)
end if
if(ij.ne.futyp%z)then
if(ij.ne.futyp%q)then
ij=futyp%sqs
exit
end if
end if
end do
stib(vmkt(0)+i1)=ij
end do
do i1=mrho,nrho
if(stib(nivd(0)+i1).gt.0)then
rotvpo(i1)=stibs(1)
do i2=1,nvert
if(i1.ne.stib(vval(0)+i2))then
cycle
end if
j1=stib(vparto(0)+i2)
do i3=1,i1
xtmp(i3)=stib(j1+i3)
end do
do i3=1,i1-1
do i4=i3+1,i1
if(xtmp(i3).gt.xtmp(i4))then
ii=xtmp(i3)
xtmp(i3)=xtmp(i4)
xtmp(i4)=ii
end if
end do
end do
go to 830
805 continue
j1=0
do i3=i1-1,1,-1
if(xtmp(i3).lt.xtmp(i3+1))then
j1=i3
exit
end if
end do
if(j1.eq.0)then
cycle
end if
j2=i1
do i3=j1+2,i1
if(xtmp(i3).le.xtmp(j1))then
j2=i3-1
exit
end if
end do
ii=xtmp(j1)
xtmp(j1)=xtmp(j2)
xtmp(j2)=ii
jj=(i1-j1)/2
j1=j1+1
do i3=0,jj-1
ii=xtmp(j1+i3)
xtmp(j1+i3)=xtmp(i1-i3)
xtmp(i1-i3)=ii
end do
830 continue
j1=stibs(1)+1
call qaoib(i1+1)
Q_ERRT
stib(j1)=i2
do i3=1,i1
stib(j1+i3)=xtmp(i3)
end do
nrot(i1)=nrot(i1)+1
go to 805
end do
j1=stibs(1)+1
call qaoib(i1+1)
Q_ERRT
stib(j1)=0
do i2=1,i1
stib(j1+i2)=nphi+1
end do
end if
end do
call qaoib(1)
Q_ERRT
stib(stibs(1))=eoa
d01: do i1=mrho,nrho
if((stib(nivd(0)+i1).gt.0).and.&
(nrot(i1).gt.1))then
h2=nrot(i1)
h1=(h2/2)+1
720 continue
if(h1.gt.1)then
h1=h1-1
ii=rotvpo(i1)+(i1+1)*(h1-1)
do i2=1,i1+1
xtmp(i2)=stib(ii+i2)
end do
else
ii=rotvpo(i1)+(i1+1)*(h2-1)
do i2=1,i1+1
xtmp(i2)=stib(ii+i2)
end do
do i2=1,i1+1
stib(ii+i2)=stib(rotvpo(i1)+i2)
end do
h2=h2-1
if(h2.eq.1)then
do i2=1,i1+1
stib(rotvpo(i1)+i2)=xtmp(i2)
end do
cycle d01
end if
end if
hj=h1
740 continue
hi=hj
hj=hi+hi
if(hj.le.h2)then
if(hj.lt.h2)then
kk=0
jj=rotvpo(i1)+(i1+1)*(hj-1)
jk=jj+i1+1
j1=1
745 continue
if(j1.le.i1)then
j1=j1+1
if(stib(jj+j1).lt.stib(jk+j1))then
kk=-1
else if(stib(jj+j1).gt.stib(jk+j1))then
kk=1
else
go to 745
end if
end if
if(kk.eq.-1)then
hj=hj+1
else if(kk.eq.0)then
mflag(mflaty%vdup)=1
end if
end if
kk=0
jj=rotvpo(i1)+(i1+1)*(hj-1)
j1=1
755 continue
if(j1.le.i1)then
j1=j1+1
if(xtmp(j1).lt.stib(jj+j1))then
kk=-1
else if(xtmp(j1).gt.stib(jj+j1))then
kk=1
else
go to 755
end if
end if
if(kk.eq.-1)then
ii=rotvpo(i1)+(i1+1)*(hi-1)
do i2=1,i1+1
stib(ii+i2)=stib(jj+i2)
end do
go to 740
else if(kk.eq.0)then
mflag(mflaty%vdup)=1
end if
end if
ii=rotvpo(i1)+(i1+1)*(hi-1)
do i2=1,i1+1
stib(ii+i2)=xtmp(i2)
end do
go to 720
end if
end do d01
if(mflag(mflaty%vdup).ne.0)then
qerrt(0)=qerrty%ale
call qmfmsg(28,0,0)
Q_ERRT
end if
do i1=mrho,nrho
if(nrot(i1).gt.0)then
ii=rotvpo(i1)
do i2=1,nrot(i1)
j1=ii+2
j2=j1+i1+1
jj=i1
84 continue
if(jj.gt.0)then
kk=stib(j2)-stib(j1)
if(kk.eq.0)then
jj=jj-1
j1=j1+1
j2=j2+1
go to 84
else if(kk.lt.0)then
qerrmsg(1:srec)='qrvi_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
end if
ii=ii+i1+1
end do
end if
end do
ii=nrho+1
dpntro(0)=stibs(1)
call qaoib(ii)
Q_ERRT
stib(stibs(1))=eoa
do i1=mrho,nrho
if(nrot(i1).gt.0)then
stib(dpntro(0)+i1)=stibs(1)
call qaoib(nphi+1)
Q_ERRT
stib(stibs(1))=nap
ii=rotvpo(i1)+2
jj=0
do i2=1,nrot(i1)+1
if(stib(ii).ne.jj)then
if(stib(ii).le.nphi)then
kk=stib(ii)
else
kk=nphi
end if
do i3=jj+1,kk
stib(stib(dpntro(0)+i1)+i3)=ii-1
end do
jj=stib(ii)
end if
ii=ii+i1+1
end do
else
stib(dpntro(0)+i1)=nap
end if
end do
stib(stibs(1))=eoa
call qsact
Q_ERRT
99 continue
return
end subroutine qrvi
subroutine qsact
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::ap(0:0),k1,k2,k3
integer(kind=c_int_least32_t)::i1,i2,j1,j2,ii,jj
ap(0)=stibs(1)
call qaoib(nphi+1)
Q_ERRT
stib(stibs(1))=eoa
k1=0
k2=0
k3=0
stib(blok(0)+1:blok(0)+nphi)=0
d01: do while(k2.lt.nphi)
do i1=k3+1,nphi
k3=i1
j2=stib(link(0)+i1)
if(stib(blok(0)+i1).eq.0)then
nblok=nblok+1
stib(blok(0)+i1)=nblok
k2=k2+1
stib(ap(0)+k2)=i1
if(stib(blok(0)+j2).eq.0)then
stib(blok(0)+j2)=nblok
k2=k2+1
stib(ap(0)+k2)=j2
end if
exit
end if
end do
if(k2.ge.nphi)then
exit d01
end if
do while(k1.lt.k2)
k1=k1+1
jj=stib(ap(0)+k1)
do i1=max(2,mrho),nrho
if(stib(dpntro(0)+i1).gt.0)then
j1=stib(stib(dpntro(0)+i1)+jj)+1
do while(stib(j1).eq.jj)
j2=stib(j1+1)
if(stib(blok(0)+j2).eq.0)then
stib(blok(0)+j2)=nblok
k2=k2+1
stib(ap(0)+k2)=j2
j2=stib(link(0)+j2)
if(stib(blok(0)+j2).eq.0)then
stib(blok(0)+j2)=nblok
k2=k2+1
stib(ap(0)+k2)=j2
end if
if(k2.ge.nphi)then
exit d01
end if
end if
j1=j1+i1+1
end do
end if
end do
end do
end do d01
if((k2.ne.nphi).or.&
(nblok.gt.nphi))then
qerrmsg(1:srec)='qsact_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
Q_ERRT
end if
do i1=1,nphi
jj=0
do i2=mrho,nrho
if(stib(nivd(0)+i2).gt.0)then
if(stib(stib(stib(dpntro(0)+i2)+i1)+1).eq.i1)then
jj=1
exit
end if
end if
end do
if(jj.eq.0)then
j1=blok(0)+i1
stib(j1)=-stib(j1)
end if
end do
ii=0
do i1=1,nphi
j1=stib(link(0)+i1)
if(stib(blok(0)+i1).lt.0)then
if(stib(blok(0)+j1).gt.0)then
ii=ii+1
end if
if(j1.le.i1)then
if(stib(blok(0)+j1).lt.0)then
nblokfp=nblokfp+1
end if
end if
end if
end do
if(nblokfp.gt.0)then
qerrt(0)=qerrty%ale
call qmfmsg(3,0,0)
Q_ERRT
else if(nblok.gt.1)then
qerrt(0)=qerrty%ale
call qmfmsg(31,0,0)
Q_ERRT
end if
if(ii.gt.0)then
qerrt(0)=qerrty%ale
call qmfmsg(8,0,0)
Q_ERRT
end if
ii=nphi+1
if(ap(0).eq.(stibs(1)-ii))then
ap(0)=nap
call qaoib(-ii)
Q_ERRT
end if
if(nblokfp.gt.0)then
do i1=1,nphi
j1=stib(link(0)+i1)
if(i1.gt.j1)then
if(stib(blok(0)+i1).lt.0)then
if(stib(blok(0)+j1).gt.0)then
stib(blok(0)+i1)=-stib(blok(0)+j1)
end if
else if(stib(blok(0)+j1).lt.0)then
if(stib(blok(0)+i1).gt.0)then
stib(blok(0)+j1)=-stib(blok(0)+i1)
end if
end if
end if
end do
j1=blok(0)
do i1=1,nphi
j1=j1+1
if(-stib(j1).gt.nblok)then
end if
end do
end if
99 continue
return
end subroutine qsact
#ifndef Q_API
subroutine qmfc
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qsty
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::i1,ifile,j1,j2,j3,nlin,slin,slinp
call qmodel
if(filc(1).gt.0)then
qerrmsg(1:srec)=' wrong type of imput file'//achar(anull)
qerrt(0)=qerrty%inp
call qmput(0,0,0)
end if
if(cflag(confi%bom).eq.0)then
if(filb(1).gt.0)then
cflag(confi%bom)=1
end if
end if
j1=2
call qopen(j1)
tfu=filu(j1)
film(1:2)=1
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
go to 07
03 continue
do i1=1,ngmk
j1=stib(gmkp(0)+i1)
j3=stib(gmkl(0)+i1)
j2=j1-1+j3
if(j3+17.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ constant :: "//stcb(j1:j2)//" ]"
else if(j3.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ constant :: ",stcb(j1:j2)," ]"
else
qerrmsg(1:srec)='qmfc_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
if(ios.ne.0)then
call qios
end if
end do
go to 65
05 continue
do i1=1,npmk
j1=stib(pmkp(0)+i1)
j3=stib(pmkl(0)+i1)
j2=j1-1+j3
if(stib(pmkd(0)+i1).gt.1)then
if(stib(pmkt(0)+i1).eq.futyp%z)then
if(j3+27.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ integer f_function :: "//stcb(j1:j2)//" ]"
else if(j3.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ integer f_function :: ",stcb(j1:j2)," ]"
else
qerrmsg(1:srec)='qmfc_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
else
if(j3+19.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ f_function :: "//stcb(j1:j2)//" ]"
else if(j3.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ f_function :: ",stcb(j1:j2)," ]"
else
qerrmsg(1:srec)='qmfc_3'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
end if
if(ios.ne.0)then
call qios
end if
end if
end do
do i1=1,npmk
j1=stib(pmkp(0)+i1)
j3=stib(pmkl(0)+i1)
j2=j1-1+j3
if(stib(pmkd(0)+i1).lt.2)then
if(stib(pmkt(0)+i1).eq.futyp%z)then
if(j3+27.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ integer p_function :: "//stcb(j1:j2)//" ]"
else if(j3.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ integer p_function :: ",stcb(j1:j2)," ]"
else
qerrmsg(1:srec)='qmfc_4'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
else
if(j3+19.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ p_function :: "//stcb(j1:j2)//" ]"
else if(j3.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ p_function :: ",stcb(j1:j2)," ]"
else
qerrmsg(1:srec)='qmfc_5'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
end if
if(ios.ne.0)then
call qios
end if
end if
end do
do i1=1,nvmk
j1=stib(vmkp(0)+i1)
j3=stib(vmkl(0)+i1)
j2=j1-1+j3
if(stib(vmkt(0)+i1).eq.futyp%z)then
if(j3+27.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ integer v_function :: "//stcb(j1:j2)//" ]"
else if(j3.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ integer v_function :: ",stcb(j1:j2)," ]"
else
qerrmsg(1:srec)='qmfc_6'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
else
if(j3+19.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ v_function :: "//stcb(j1:j2)//" ]"
else if(j3.lt.srec)then
write(unit=tfu,fmt='(a,/)',iostat=ios)" [ v_function :: ",stcb(j1:j2)," ]"
else
qerrmsg(1:srec)='qmfc_7'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
end if
if(ios.ne.0)then
call qios
end if
end do
if(npmk+nvmk.gt.0)then
write(unit=tfu,fmt='(a,/)',iostat=ios)
if(ios.ne.0)then
call qios
end if
end if
go to 65
07 continue
ifile=1
rewind(unit=filu(ifile),iostat=ios)
if(ios.ne.0)then
call qios
end if
nlin=0
slinp=-1
if(iamk.eq.0)then
if(stofc.gt.0)then
qerrt(0)=qerrty%inp
call qiomsg(6,0,0,0)
end if
end if
10 continue
call qrr(ifile,nlin)
slin=recdty(recty%len)
if(slin.lt.0)then
go to 85
end if
if(jflag(jflaty%mflang).eq.0)then
if(nlin.eq.nlin34a)then
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
go to 03
end if
if(nlin.gt.nlin34b)then
if(nlin34b.ge.0)then
if(nlin34a.gt.0)then
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
end if
nlin34a=-1
nlin34b=-1
if(npmk+nvmk.gt.0)then
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
go to 05
end if
end if
end if
end if
if(slin.eq.0)then
if(nlin.eq.1)then
go to 10
end if
end if
65 continue
j1=stcbs(1)+1
j2=stcbs(1)+slin
serrt=qerrty%ok
if(slin.gt.0)then
if(iachar(stcb(j2:j2)).eq.aspc)then
serrt=qerrty%q
else if(iachar(stcb(j2+1:j2+1)).ne.alf)then
serrt=qerrty%q
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='invalid record read from model-file'//achar(anull)
qerrt(0)=serrt
call qmput(nlin,nlin,0)
end if
if(recdty(recty%annot).eq.0)then
j3=j2+1
call qnapa(stcb,j1,j3,qfty%mtyp)
j2=j3-1
nstjb=0
end if
end if
if(serrt.le.qerrty%ale)then
if(recdty(recty%len).eq.0)then
write(unit=tfu,fmt='(a)',iostat=ios)
else if(recdty(recty%annot).ne.0)then
if(iamk.ne.0)then
j3=iachar(stcb(j1:j1))
do i1=j1,j2
if(iachar(stcb(i1:i1)).ne.j3)then
exit
end if
stcb(i1:i1)=achar(iamk)
end do
end if
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)
else if(recdty(recty%tail).eq.arsbr)then
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)
else if(recdty(recty%tail).ne.abslash)then
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)//' \'
else
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)
end if
end if
if(ios.ne.0)then
call qios
end if
slinp=slin
go to 10
85 continue
if(slinp.gt.0)then
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
end if
if(nstjb.ne.0)then
qerrmsg(1:srec)='qmfc_8'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
call qclose(0)
99 continue
return
end subroutine qmfc
subroutine qmbc
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles
use,non_intrinsic::qimodel
use,non_intrinsic::qintr
use,non_intrinsic::qmix
use,non_intrinsic::qproc
use,non_intrinsic::qwbuffer
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::i1,i2,j1,j2,j3,j4,j7,jj,l0,njb
njb=nstjb
mrho=maxdeg
nrho=0
call qmodel
if(cflag(confi%bom).eq.0)then
if(filb(1).gt.0)then
cflag(confi%bom)=1
end if
end if
j1=2
call qopen(j1)
tfu=filu(j1)
film(1:2)=1
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
if(ngmk.gt.0)then
do i1=1,ngmk
j1=stib(gmkp(0)+i1)
j2=stib(gmkl(0)+i1)+(j1-1)
if(stofc.eq.-4)then
l0=15
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ constant :: "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(j1,j2,0)
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" ]"
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(0,0,0)
end if
l0=3
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(j1,j2,0)
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)="= "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
j3=stib(gmkvp(0)+i1)
j4=stib(gmkvl(0)+i1)+(j3-1)
call qctomw(j3,j4,1)
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" ]"
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(0,0,0)
call qctomw(0,0,0)
end do
end if
if(stofc.eq.-4)then
if(npmk.gt.0)then
do i1=1,npmk
j1=stib(pmkp(0)+i1)
j2=stib(pmkl(0)+i1)+(j1-1)
l0=17
call qvaocb(l0)
if(stib(pmkd(0)+i1).lt.2)then
if(stib(pmkt(0)+i1).eq.futyp%z)then
l0=25
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ integer p_function :: "
else
l0=17
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ p_function :: "
end if
else
if(stib(pmkt(0)+i1).eq.futyp%z)then
l0=25
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ integer f_function :: "
else
l0=17
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ f_function :: "
end if
end if
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(j1,j2,0)
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" ]"
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(0,0,0)
call qctomw(0,0,0)
end do
end if
if(nvmk.gt.0)then
do i1=1,nvmk
j1=stib(vmkp(0)+i1)
j2=stib(vmkl(0)+i1)+(j1-1)
if(stib(vmkt(0)+i1).eq.futyp%z)then
l0=25
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ integer v_function :: "
else
l0=17
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ v_function :: "
end if
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(j1,j2,0)
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" ]"
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(0,0,0)
call qctomw(0,0,0)
end do
end if
end if
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
do i1=1,nphi
j7=stib(link(0)+i1)
if(i1.gt.j7)then
cycle
end if
l0=3
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
j1=stib(namep(0)+i1)
j2=stib(namel(0)+i1)+(j1-1)
j3=stib(namep(0)+j7)
j4=stib(namel(0)+j7)+(j3-1)
call qctomw(j1,j2,0)
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(j3,j4,0)
if(stofc.eq.-4)then
l0=4
call qvaocb(l0)
if(stib(antiq(0)+i1).eq.0)then
stcb(stcbs(1)+1:stcbs(1)+l0)=", +1"
else
stcb(stcbs(1)+1:stcbs(1)+l0)=", -1"
end if
else
l0=3
call qvaocb(l0)
if(stib(antiq(0)+i1).eq.0)then
stcb(stcbs(1)+1:stcbs(1)+l0)=", +"
else
stcb(stcbs(1)+1:stcbs(1)+l0)=", -"
end if
end if
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
jj=stib(tpc(0)+i1)
if(jj.ne.phity%dflt)then
if(jj.eq.phity%ext)then
l0=10
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", external"
else if(jj.eq.phity%notdp)then
l0=11
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", notadpole"
end if
if(stofc.eq.-2)then
if(jj.eq.phity%ntint)then
l0=11
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", notadpole"
end if
else
if(jj.eq.phity%ntint)then
l0=21
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", notadpole, internal"
else if(jj.eq.phity%int)then
l0=10
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", internal"
end if
end if
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
end if
if(npmk.gt.0)then
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)="; "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
do i2=1,npmk
j1=stib(pmkp(0)+i2)
j2=stib(pmkl(0)+i2)+(j1-1)
call qctomw(j1,j2,0)
if(stib(pmkd(0)+i2).lt.2)then
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)="= "
else
l0=3
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)="= ("
end if
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
j1=stib(stib(pmkvfpp(0)+i1)+i2)
j2=stib(stib(pmkvflp(0)+i1)+i2)+(j1-1)
call qctomw(j1,j2,1)
if(stib(pmkd(0)+i2).gt.1)then
if(i1.ne.j7)then
j3=stib(stib(pmkvfpp(0)+j7)+i2)
j4=stib(stib(pmkvflp(0)+j7)+i2)+(j3-1)
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(j3,j4,1)
end if
l0=1
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=")"
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
end if
if(i2.lt.npmk)then
l0=3
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
end if
end do
end if
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" ]"
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(0,0,0)
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
end do
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
do i1=1,nvert
l0=3
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" [ "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
jj=stib(vparto(0)+i1)
do i2=1,stib(vval(0)+i1)
j1=stib(namep(0)+stib(jj+i2))
j2=stib(namel(0)+stib(jj+i2))+(j1-1)
call qctomw(j1,j2,0)
if(i2.lt.stib(vval(0)+i1))then
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
end if
end do
if(nvmk.gt.0)then
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)="; "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
do i2=1,nvmk
j1=stib(vmkp(0)+i2)
j2=stib(vmkl(0)+i2)+(j1-1)
call qctomw(j1,j2,0)
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)="= "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
j1=stib(vmkvpp(0)+i2)
j2=stib(vmkvlp(0)+i2)
j3=stib(j1+i1)
j4=stib(j2+i1)+(j3-1)
call qctomw(j3,j4,1)
if(i2.lt.nvmk)then
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=", "
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
end if
end do
end if
l0=2
call qvaocb(l0)
stcb(stcbs(1)+1:stcbs(1)+l0)=" ]"
call qctomw(stcbs(1)+1,stcbs(1)+l0,0)
call qctomw(0,0,0)
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
end do
call qclose(0)
99 continue
return
end subroutine qmbc
subroutine qctomw(j1,j2,imgt)
use,non_intrinsic::qaski
use,non_intrinsic::qbounds
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles,only:non_unit
use,non_intrinsic::qimodel
use,non_intrinsic::qwbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::imgt,j1,j2
integer(kind=c_int_least32_t)::i1,ll,stdl
integer(kind=c_int_least32_t)::ll0=0
character(kind=asciik,len=srec)::s0
if(stofc.eq.-4)then
stdl=srec-1
else
stdl=srec0-1
end if
ll=(j2-j1)+1
if((ll.lt.0).or.&
(stdl+1.lt.srec0).or.&
(modulo(stdl,2).ne.0).or.&
(tfu.eq.non_unit))then
qerrmsg(1:srec)='qctomw_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
if(j2.eq.0)then
if(ll0.gt.0)then
write(unit=tfu,fmt='(a)',iostat=ios)s0(1:ll0)
ll0=0
else
write(unit=tfu,fmt='(a)',iostat=ios)
end if
if(ios.ne.0)then
call qios
end if
else
if(imgt.ne.0)then
if(stofc.eq.-4)then
if(ll0.gt.stdl-8)then
write(unit=tfu,fmt='(a)',iostat=ios)s0(1:ll0)//"\"
ll0=0
end if
else
if(ll0.gt.stdl-6)then
write(unit=tfu,fmt='(a)',iostat=ios)s0(1:ll0)//"\"
ll0=0
end if
end if
if(ios.ne.0)then
call qios
end if
if((j1.gt.j2).or.&
((j1.le.j2).and.(iachar(stcb(j2:j2)).ne.asq)))then
ll0=ll0+1
s0(ll0:ll0)="'"
end if
do i1=j1,j2
ll0=ll0+1
s0(ll0:ll0)=stcb(i1:i1)
if(iachar(stcb(i1:i1)).eq.asq)then
if(i1.ne.j1)then
if(i1.ne.j2)then
ll0=ll0+1
s0(ll0:ll0)=stcb(i1:i1)
end if
end if
end if
if(i1.lt.j2)then
if(stofc.eq.-4)then
if(ll0.gt.stdl-8)then
write(unit=tfu,fmt='(a)',iostat=ios)s0(1:ll0)//"' \"
ll0=2
s0(1:ll0)=" '"
end if
else
if(ll0.gt.stdl-6)then
write(unit=tfu,fmt='(a)',iostat=ios)s0(1:ll0)//"'"
ll0=2
s0(1:ll0)=" '"
end if
end if
end if
if(ios.ne.0)then
call qios
end if
end do
if((j1.gt.j2).or.&
((j1.le.j2).and.(iachar(stcb(j2:j2)).ne.asq)))then
ll0=ll0+1
s0(ll0:ll0)="'"
end if
else if(j1.le.j2)then
if(ll0+ll.gt.stdl-3)then
if(stofc.eq.-4)then
write(unit=tfu,fmt='(a)',iostat=ios)s0(1:ll0)//" \"
ll0=0
else
write(unit=tfu,fmt='(a)',iostat=ios)s0(1:ll0)
ll0=0
end if
if(ios.ne.0)then
call qios
end if
if(ll.gt.stdl-3)then
if(stofc.eq.-4)then
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)//" \"
ll0=0
else
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)
ll0=0
end if
if(ios.ne.0)then
call qios
end if
else
s0(1:ll)=stcb(j1:j2)
ll0=ll
end if
else
s0(ll0+1:ll0+ll)=stcb(j1:j2)
ll0=ll0+ll
end if
end if
end if
99 continue
return
end subroutine qctomw
subroutine qsfc
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qsty
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t), external::qstykifc,qudstyk
integer(kind=c_int_least32_t)::f0,f1,ieosf,isec,lgm,slin,nblin
integer(kind=c_int_least32_t)::ii,ij,i0,i1,i1p,i2,jj,j1,j2,kp1,kp2,k1,k2,delt
integer(kind=c_int_least32_t)::clin(1:sfiles0),nlin(1:sfiles0)
integer(kind=c_int_least32_t)::dlin(1:sfiles0),ddlin(1:sfiles0)
character(kind=asciik,len=2*srec)::styb
integer(kind=c_int_least32_t)::kk
nskec=0
call qspak('677977776578686376797980;',nskec,0,0,0)
call qspak('6779777765786863767378696376797980;',nskec,0,0,0)
call qspak('677977776578686368658465;',nskec,0,0,0)
call qspak('68736571826577637378686988;',nskec,0,0,0)
call qspak('687365718265776367798578846982;',nskec,0,0,0)
call qspak('8384658469776978846376797980;',nskec,0,0,0)
call qspak('838465846977697884638385666376797980;',nskec,0,0,0)
call qspak('83856663838465846977697884;',nskec,0,0,0)
call qspak('838465846977697884638385666376797980302883856663838465846977697884;',nskec,0,0,0)
call qspak('2869786830;',nskec,0,0,0)
call qspak('677977776578686368658465302866656775;',nskec,0,0,0)
kk=2
call qaoib(kk)
stib(stibs(1)-(kk-1):stibs(1))=eoa
ii=nskec+1
call qtrm(kk,ii,stibs(1))
wskec(0)=stibs(1)-ii
pskec(0)=wskec(0)-ii
do i1=1,njpq
jp(i1)=stib(pskec(0)+i1)
jq(i1)=jp(i1)-1+stib(wskec(0)+i1)
end do
nblin=0
j1=0
do i1=1,nfiles
if(filt(i1).eq.qfty%styp)then
if(cflag(confi%bom).eq.0)then
if(filb(i1).gt.0)then
cflag(confi%bom)=1
end if
end if
if(filp(i1).ne.nap)then
call qopen(i1)
jj=2
call qopen(jj)
tfu=filu(jj)
film(1:2)=1
end if
j1=j1+1
nlin(j1)=0
dlin(j1)=0
ddlin(j1)=0
end if
end do
ks=0
call qaoib(2)
udkp(1)=stibs(1)-1
stib(udkp(1))=eoa
stib(stibs(1))=eoa
isec=-1
04 continue
if(isec.gt.0)then
call qaoib(1)
stib(stibs(1))=eosf
end if
isec=isec+1
if(isec.gt.4)then
go to 99
end if
if(isec.gt.0)then
iogp(isec)=stibs(1)+1
end if
ieosf=0
f0=0
10 continue
f0=f0+1
if(f0.gt.nfiles)then
go to 04
else if(filp(f0).eq.nap)then
go to 10
else if(filt(f0).ne.qfty%styp)then
go to 10
end if
f1=film(f0)
if(abs(isec-2).lt.2)then
call qaoib(2)
if(f1.gt.1)then
stib(ieosf)=stibs(1)-ieosf
end if
ieosf=stibs(1)
stib(ieosf-1)=eosf
end if
clin(f1)=0
20 continue
if(nlin(f1).gt.0)then
if(i0.lt.slin)then
write(unit=tfu,fmt='(a)',iostat=ios)styb(i0+1:slin)
if(ios.ne.0)then
call qios
end if
nblin=0
end if
end if
i0=0
i1p=0
delt=4
call qrr(f0,nlin(f1))
recdty(recty%annot)=0
slin=recdty(recty%len)
if(nlin(f1).eq.1)then
if((abs(isec-2).le.1).or.&
(nblin.lt.blines0))then
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
nblin=nblin+1
end if
if(slin.eq.0)then
go to 20
end if
end if
if(slin.lt.0)then
if(isec.lt.4)then
call qstymsg(1,0,0,f0,0,0)
end if
go to 10
else if(slin.eq.0)then
if((abs(isec-2).le.1).or.&
(nblin.lt.blines0))then
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
nblin=nblin+1
end if
go to 20
end if
styb(1:slin+1)=stcb(stcbs(1)+1:stcbs(1)+slin)//achar(alf)
ij=0
if(clin(f1).eq.0)then
j1=iachar(styb(1:1))
j2=iachar(styb(slin:slin))
if((j1.eq.alt).and.&
(j2.eq.agt))then
ij=qstykifc(styb,2,slin-1,isec)
if(ij.gt.0)then
if(stib(kla(0)+ij).eq.0)then
if(ij-1.ne.isec)then
go to 80
else if(ks.ne.0)then
go to 80
end if
if(recdty(recty%xchar).ne.0)then
go to 80
end if
if(ij.eq.1)then
dlin(f1)=nlin(f1)+1
end if
go to 10
end if
end if
end if
end if
if(recdty(recty%xchar).ne.0)then
if((cflag(confi%xchar).lt.0).or.&
(abs(isec-2).lt.2))then
qerrt(0)=qerrty%inp
call qiomsg(17,nlin(f1),nlin(f1),f0)
end if
end if
if(abs(isec-2).eq.2)then
j1=iachar(styb(1:1))
if(acf(j1).eq.chty%annot)then
recdty(recty%annot)=1
if(j1.eq.aast)then
if(stofc.lt.0)then
qerrt(0)=qerrty%inp
call qiomsg(16,nlin(f1),nlin(f1),f0)
end if
else if(fila(f0).eq.0)then
fila(f0)=j1
else if(fila(f0).ne.j1)then
if(stofc.lt.0)then
qerrt(0)=qerrty%inp
call qiomsg(16,nlin(f1),nlin(f1),f0)
end if
end if
if(iamk.gt.0)then
do i1=1,slin
if(iachar(styb(i1:i1)).ne.j1)then
exit
end if
styb(i1:i1)=achar(iamk)
end do
else
i0=slin
end if
go to 20
else
go to 80
end if
else if(clin(f1).ne.0)then
go to 80
end if
j1=0
j2=0
k1=0
k2=0
kp1=0
kp2=0
lgm=0
i1=0
do while(i1.lt.slin)
i1=i1+1
jj=iachar(styb(i1:i1))
if((j2.eq.0).and.&
(jj.eq.alt))then
j1=j1+1
if(j1.eq.2)then
call qaoib(1)
stib(stibs(1))=jj
j1=0
else if(iachar(styb(i1+1:i1+1)).ne.alt)then
if(lgm.ne.0)then
go to 80
end if
lgm=1-lgm
kp1=i1+1
end if
else if((j1.eq.0).and.&
(jj.eq.alsbr))then
j2=j2+1
if(j2.eq.2)then
call qaoib(1)
stib(stibs(1))=jj
j2=0
else if(iachar(styb(i1+1:i1+1)).ne.alsbr)then
if(j1.ne.0)then
go to 80
else if(lgm.ne.0)then
go to 80
end if
lgm=1-lgm
kp1=i1+1
end if
else if((j2.eq.0).and.&
(jj.eq.agt))then
if(j1.eq.0)then
k1=k1+1
if(k1.eq.2)then
call qaoib(1)
stib(stibs(1))=jj
k1=0
else if(iachar(styb(i1+1:i1+1)).ne.agt)then
go to 80
end if
else
if(lgm.eq.0)then
go to 80
end if
lgm=1-lgm
j1=0
kp2=i1-1
if(kp2-kp1.lt.0)then
go to 80
end if
ii=qstykifc(styb,kp1,kp2,isec)
if(tofc.eq.fcty%sc)then
if((ii.eq.18).or.&
(ii.eq.34).or.&
(ii.eq.36).or.&
(ii.eq.38).or.&
(ii.eq.55).or.&
(ii.eq.57).or.&
(ii.eq.67).or.&
(ii.eq.68).or.&
(ii.eq.72).or.&
(ii.eq.73).or.&
(ii.eq.82).or.&
(ii.eq.86).or.&
(ii.eq.87))then
ii=-1
end if
if(abs(isec-2).eq.1)then
if((ii.eq.13).or.&
(ii.eq.14))then
ii=-1
end if
end if
if(stofc.gt.0)then
if((ii.eq.11).or.&
(ii.eq.12).or.&
(ii.eq.90))then
ii=-1
end if
end if
if(stofc.lt.0)then
if(ii.eq.81)then
if(isec.ne.3)then
ii=-1
end if
end if
end if
if(stofc.eq.-2)then
if((ii.eq.63).or.&
(ii.eq.64).or.&
(ii.eq.65).or.&
(ii.eq.66).or.&
(ii.eq.83).or.&
(ii.eq.85))then
ii=-1
end if
end if
end if
if(ii.eq.91)then
if(isec.ne.1)then
go to 80
else if(nlin(f1).ne.dlin(f1))then
go to 80
end if
if((ddlin(f1).eq.0).or.&
(ddlin(f1).eq.2))then
ddlin(f1)=ddlin(f1)+1
end if
else if(nlin(f1).eq.dlin(f1))then
if(ddlin(f1).lt.2)then
ddlin(f1)=ddlin(f1)+2
end if
end if
if(ii.le.0)then
if(ii.eq.0)then
go to 80
else if(stofc.gt.0)then
go to 80
else
call qstymsg(13,0,0,0,0,0)
end if
else if(ii.lt.5)then
if((kp1.ne.2).or.&
(kp2+1.ne.slin))then
go to 80
else if((ks.ne.0).or.&
(clin(f1).ne.0))then
go to 80
end if
else if(clin(f1).eq.0)then
call qktoc(isec,ii,nlin(f1),f0)
else
qerrmsg(1:srec)='qsfc_1'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
if(isec.eq.3)then
if(stofc.lt.0)then
if(ii.eq.81)then
call qksu(styb,kp1,jp(5),jq(5),jp(4),jq(4),i1,slin)
go to 30
end if
else
if(ii.eq.80)then
call qksu(styb,kp1,jp(4),jq(4),jp(5),jq(5),i1,slin)
go to 30
end if
end if
end if
if(abs(isec-2).eq.1)then
i2=slin
if(stofc.lt.0)then
if(ii.eq.11)then
call qksu(styb,kp1,jp(6),jq(6),jp(1),jq(1),i1,slin)
else if(ii.eq.12)then
call qksu(styb,kp1,jp(7),jq(7),jp(2),jq(2),i1,slin)
else if(ii.eq.90)then
call qksu(styb,kp1,jp(8),jq(8),jp(11),jq(11),i1,slin)
end if
else
if(ii.eq.101)then
call qksu(styb,kp1,jp(1),jq(1),jp(6),jq(6),i1,slin)
else if(ii.eq.102)then
call qksu(styb,kp1,jp(2),jq(2),jp(7),jq(7),i1,slin)
else if(ii.eq.100)then
if(ks.eq.1)then
call qksu(styb,kp1,jp(3),jq(3),jp(9),jq(9),i1,slin)
kp2=kp2+(slin-i2)
write(unit=tfu,fmt='(a)',iostat=ios)styb(1:kp2+1)
i0=kp2+1
call qksu(styb,i0+1,0,0,jp(10),jq(10),i1,slin)
nblin=0
else if(ks.eq.2)then
call qksu(styb,kp1,jp(3),jq(3),jp(8),jq(8),i1,slin)
kp2=kp2+(slin-i2)
write(unit=tfu,fmt='(a)',iostat=ios)styb(1:kp2+1)
i0=kp2+1
nblin=0
end if
if(ios.ne.0)then
call qios
end if
if(i0.eq.slin)then
end if
end if
end if
end if
end if
else if((j1.eq.0).and.&
(jj.eq.arsbr))then
if(j2.eq.0)then
k2=k2+1
if(k2.eq.2)then
call qaoib(1)
stib(stibs(1))=jj
k2=0
else if(iachar(styb(i1+1:i1+1)).ne.arsbr)then
go to 80
end if
else
j2=0
if(j1.ne.0)then
go to 80
else if(lgm.eq.0)then
go to 80
end if
lgm=1-lgm
kp2=i1-1
if(kp2-kp1.lt.0)then
go to 80
end if
if(clin(f1).ne.0)then
qerrmsg(1:srec)='qsfc_2'//achar(anull)
qerrt(0)=qerrty%q
call qmput(0,0,0)
end if
ii=qudstyk(styb,kp1,kp2)
if(ii.eq.0)then
go to 80
end if
end if
else if((j1.eq.0).and.&
(j2.eq.0))then
if(clin(f1).eq.0)then
call qaoib(1)
stib(stibs(1))=jj
else if(jj.ne.aspc)then
if(abs(isec-2).lt.2)then
go to 80
end if
end if
end if
30 continue
if(j1.eq.0)then
if(j2.eq.0)then
if(k1.eq.0)then
if(k2.eq.0)then
if(i1-i1p.gt.srec0-(delt-3))then
call qstymsg(14,0,0,0,0,0)
end if
if(i1-i0.gt.srec0-delt)then
if(i1p.gt.0)then
if(iachar(styb(i1p:i1p)).eq.aspc)then
write(unit=tfu,fmt='(a,/,a)',iostat=ios)styb(i0+1:i1p)//".","<back><back>"
i0=i1p
else
write(unit=tfu,fmt='(a)',iostat=ios)styb(i0+1:i1p)
i0=i1p
end if
if(ios.ne.0)then
call qios
end if
write(unit=tfu,fmt='(a)',advance='no',iostat=ios)"<back>"
if(ios.ne.0)then
call qios
end if
nblin=0
delt=10
end if
if(i1-i1p.gt.srec0-(delt-3))then
call qstymsg(14,0,0,0,0,0)
end if
if(i1-i1p.gt.srec0-delt)then
write(unit=tfu,fmt='(a)',iostat=ios)styb(i1p+1:i1)
if(ios.ne.0)then
call qios
end if
i0=i1
nblin=0
if(i1.lt.slin)then
write(unit=tfu,fmt='(a)',advance='no',iostat=ios)"<back>"
if(ios.ne.0)then
call qios
end if
delt=10
end if
end if
end if
i1p=i1
end if
end if
end if
end if
end do
if(lgm.ne.0)then
go to 80
end if
if(clin(f1).ne.0)then
go to 20
end if
call qaoib(1)
stib(stibs(1))=alf
go to 20
80 continue
if(clin(f1).eq.0)then
ii=nlin(f1)
else
ii=clin(f1)
end if
qerrmsg(1:srec)="wrong syntax,"//achar(anull)
qerrt(0)=qerrty%inp
call qmput(ii,nlin(f1),f0)
99 continue
return
end subroutine qsfc
subroutine qksu(s,j3,k1,k2,k3,k4,ix,slin)
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t),intent(in)::j3,k1,k2,k3,k4
integer(kind=c_int_least32_t),intent(inout)::ix,slin
character(kind=asciik,len=2*srec),intent(inout)::s
integer(kind=c_int_least32_t)::j4,l0,dl1,xl1,i1
if(k1.gt.0)then
l0=k2-k1+1
else
l0=0
end if
xl1=k4-k3
dl1=xl1-(l0-1)
j4=j3+l0
if(dl1.gt.0)then
call qaocb(dl1)
do i1=slin,j4,-1
s(i1+dl1:i1+dl1)=s(i1:i1)
end do
else if(dl1.lt.0)then
do i1=j4,slin
s(i1+dl1:i1+dl1)=s(i1:i1)
end do
end if
slin=slin+dl1
ix=ix+dl1
s(j3:j3+xl1)=stcb(k3:k4)
99 continue
return
end subroutine qksu
subroutine qbfc
use,non_intrinsic::qaski
use,non_intrinsic::qcbuffer
use,non_intrinsic::qfcon
use,non_intrinsic::qfiles
use,non_intrinsic::qintr
use,non_intrinsic::qzbuffer
use,non_intrinsic::qbasic
implicit none
save
integer(kind=c_int_least32_t)::ifile,i1,j0,j1,j2,j3,j4,k0,k1,k2,k3,k4,nlin,nblin,slin,slinp,njb
ifile=1
call qopen(ifile)
if(cflag(confi%bom).eq.0)then
if(filb(1).gt.0)then
cflag(confi%bom)=1
end if
end if
ifile=2
call qopen(ifile)
tfu=filu(ifile)
film(1:ifile)=1
ifile=1
nlin=0
nblin=0
slinp=-1
njb=nstjb
10 continue
call qrr(ifile,nlin)
slin=recdty(recty%len)
if(slin.lt.0)then
go to 85
end if
j1=stcbs(1)+1
j2=stcbs(1)+slin
serrt=qerrty%ok
if(stofc.lt.0)then
if(recdty(recty%annot).ne.0)then
slin=0
end if
end if
if(slin.gt.0)then
if(iachar(stcb(j2:j2)).eq.aspc)then
serrt=qerrty%q
else if(iachar(stcb(j2+1:j2+1)).ne.alf)then
serrt=qerrty%q
end if
if(stofc.gt.0)then
if(slin.ge.srec0)then
serrt=qerrty%inp
else if(iachar(stcb(j2:j2)).eq.abslash)then
if(recdty(recty%annot).eq.0)then
serrt=qerrty%inp
end if
end if
end if
if(stofc.lt.0)then
if(iachar(stcb(j2:j2)).eq.abslash)then
j3=0
do i1=j2-1,j1,-1
if(iachar(stcb(i1:i1)).ne.aspc)then
j2=i1
j3=1
slin=(j2-j1)+1
exit
end if
end do
if(j3.eq.0)then
serrt=qerrty%inp
end if
end if
end if
if(serrt.ne.qerrty%ok)then
qerrmsg(1:srec)='invalid record read from control-file'//achar(anull)
qerrt(0)=serrt
call qcfmsg0(1,nlin,nlin)
end if
end if
if(nlin.eq.1)then
if(slin.gt.0)then
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
nblin=1
end if
end if
if(serrt.le.qerrty%ale)then
if(slin.eq.0)then
if(nblin.lt.blines0)then
write(unit=tfu,fmt='(a)',iostat=ios)
end if
else if(recdty(recty%annot).ne.0)then
if(iamk.gt.0)then
j3=iachar(stcb(j1:j1))
do i1=j1,j2
if(iachar(stcb(i1:i1)).eq.j3)then
stcb(i1:i1)=achar(iamk)
else
exit
end if
end do
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)
end if
else if(recdty(recty%tail).eq.ascol)then
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)
else
if(stofc.gt.0)then
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)//' \'
else if(recdty(recty%len).le.srec0)then
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j1:j2)
else
call qnapa(stcb,j1,j2,qfty%ctyp)
j0=1
do i1=1,stjb(stjbs-1)
if(stjb(3*j0).eq.strty%sqs)then
k0=2
else
k0=1
end if
k1=stjb(3*j0+k0)
k2=stjb(3*i1+2)
k3=(k2-k1)+1
if(k3.ge.srec0)then
if(i1.gt.j0)then
write(unit=tfu,fmt='(a)',iostat=ios)stcb(stjb(3*j0+k0):stjb(3*i1-1))
if(ios.ne.0)then
call qios
end if
j0=i1
else if(k0.eq.2)then
j3=k1
do while(j3.le.k3)
k4=min(k2-j3,srec0-3)
write(unit=tfu,fmt='(a)',iostat=ios)stcb(j3:j4)
if(ios.ne.0)then
call qios
end if
j3=j4+1
end do
else
qerrt(0)=qerrty%inp
call qiomsg(18,0,0,1)
end if
else if(i1.eq.stjb(stjbs-1))then
write(unit=tfu,fmt='(a)',iostat=ios)stcb(stjb(3*j0+k0):stjb(3*i1+2))
if(ios.ne.0)then
call qios
end if
end if
end do
end if
end if
if(ios.ne.0)then
call qios
end if
if(slin.gt.0)then
nblin=0
else
nblin=nblin+1
end if
end if
slinp=slin
if(njb.lt.nstjb)then
call qaojb(-1)
end if
go to 10
85 continue
if(slinp.gt.0)then
if(nblin.lt.blines0)then
write(unit=tfu,fmt='(a)',iostat=ios)
if(ios.ne.0)then
call qios
end if
end if
end if
call qclose(0)
99 continue
return
end subroutine qbfc
program qgraf
use,non_intrinsic::qintr,only:cflag,qxmod,dsplmod,qsgnl
use,non_intrinsic::qkeys,only:confi,qmod
use,non_intrinsic::qbasic
implicit none
save
external::qinputs,qgen
qxmod=qmod%auto
cflag(confi%dspl)=dsplmod%info
call qinputs
qsgnl=1
do while(qsgnl.ne.0)
call qgen
end do
stop
end program qgraf
#endif
