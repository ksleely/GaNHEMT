program ganhemtNew01;
uses dos, crt, graph;
const
   zm       = 1021; { total number of pixels }
   layer    = 3;
   nsubMax  = 15;   { maximum number of subbands considered in this program }
   chrg     = 1.602177; { unit charge }
   epsilon0 = 8.85418;
type
  Varray     = array[0..zm] of Real;
  Larray     = array[1..layer] of Real;
  Earray     = array[0..nsubMax] of Real;
  PsiArray   = array[0..nsubMax,0..zm] of Real;
  zarray     = array[0..nsubMax] of integer;
var
  z1,z2,z3, zmax, zmin, zpdop1, zpdop2, zndop1,zndop2 : integer;
  Vsub, T_k, kT, Vgs, dz:real;
  chrgden, ionaden, iondden, eden, nelec : real;
  backden, iaden, idden, freechrg : real;

  Alz, Inz, pol, epsi, bandgap, Vh, thick: Larray;
  sfcden, AlxSub, InxSub, xexp : real;
  Fact1, Fact2, dVSq, Mw, Mb, EFermi, Fermibuffer, thickbuff : real;
  SurfaceFac, FPenergy, donorden, beAc, bedon,
  acceptorden  : real;
  V0, V, Psi, phi, RhoA, Rhod : Varray;
  nMax, Yscale, Yoffset, Xoffset, Xscale: integer;
  Energy, sub_density : Earray;
  zfirst, zlast : zarray;
  PsiSq :PsiArray;
  fixedNMax: boolean;

Procedure Inigraph;
var
  gd, gm, error : smallint;
  dummy : smallint;
begin
 { We have an 8 bit mode  as the default}
  gd := d8bit;
  gm := m640x480;
  getModeRange(gd,dummy,gm);
  initgraph(gd,gm,'');
  { Make sure you always check graphresult! }
  error := graphResult;
  if (error <> grOk) then begin
     Writeln('graph driver ',gd,' graph mode ',gm,' not supported');
     halt(1)
  end;
  SetViewPort(0,0,getmaxx,getmaxy, clipoff);
  Setbkcolor(black);
  setcolor(white);
  setTextStyle(defaultFont,horizdir,1);
  clearViewPort;
  cleardevice;
  Yoffset := getmaxy-round(100.0*dz);
  Yscale := round(2.0*dz);
  Xoffset := 450;
  Xscale := round(dz);
end;

function Abc (x, g_Ac, g_bc, bowing : real): real;
var y, g : real;
begin
  y := 1.0-x;
  g := y*g_Ac + x*g_bc - x*y*bowing;
  Abc := g;
end;

function Eg0_AlIngan(Al,Iny:real):real;
const
  gan0_g   = 3.507; {eV, T = 0K}
  Aln0_g   = 6.23; {eV, T = 0K}
  Inn0_g   = 1.4; {1.994;} {eV, should be corrected}
var
 u, v, w, ga, gan_g, Aln_g, Inn_g : real;
 gan, Aln, Inn , bow_Algan, bow_AlInn, bow_gaInn : real;
 gaAl, AlIn, gaIn, temp, deno: real;
 alpha_gan, beta_gan : real;
 alpha_Aln, beta_Aln : real;
 alpha_Inn, beta_Inn : real;
begin
 ga := 1.0 - Al - Iny;
 bow_Algan := 1.0;  {0.44 : by Voznyy et al. Semicond. v.38, p.316 (04)}
 bow_AlInn := 4.16; {calculated by Voznyy et al.}
 bow_gaInn := 1.43; {Ager III et al. Proc. of SPIE v.5530, p.308}
             {2.72 : Voznyy et al.}
 alpha_gan := 0.909; {meV/K}
 beta_gan := 830.0; {K}
 gan_g := gan0_g - 1.0e-3*alpha_gan*sqr(T_k)/(T_k + beta_gan);
 alpha_Aln := 1.799; {meV/K}
 beta_Aln := 1462.0; {K}
 Aln_g := Aln0_g - 1.0e-3*alpha_Aln*sqr(T_k)/(T_k + beta_Aln);
 alpha_Inn := 0.245; {meV/K}
 beta_Inn := 624.0; {K}
 Inn_g := Inn0_g - 1.0e-3*alpha_Inn*sqr(T_k)/(T_k + beta_Inn);
 if ga < 1e-2 then
  temp := Al*Aln_g + Iny*Inn_g - Al*Iny*bow_AlInn
 else begin
  if Iny < 1e-2 then
   temp := ga*gan_g + Al*Aln_g - ga*Al*bow_Algan
  else begin
   if Al < 1e-2 then
     temp := ga*gan_g + Iny*Inn_g - ga*Iny*bow_gaInn
   else begin
    deno := ga*Al +Al*Iny + Iny*ga;
    u := (1.0 - ga + Al)/2.0;
    v := (1.0 - Al + Iny)/2.0;
    w := (1.0 - Iny + ga)/2.0;
    gan := gan_g;
    Aln := Aln_g;
    Inn := Inn_g;
    gaAl := Abc(u, gan, Aln, bow_Algan);
    AlIn := Abc(v, Aln, Inn, bow_AlInn);
    gaIn := Abc(w, Inn, gan, bow_gaInn);
    temp := (ga*Al*gaAl + Al*Iny*AlIn + Iny*ga*gaIn)/deno;
   end
  end
 end;
 Eg0_AlIngan := temp;
end;

function calbandgap(Alx,Iny:real):real;
const
  a0_gan  =  3.189;  {a-lattice parameter}
  a0_Aln  =  3.112;
  a0_Inn = 3.545;
  c13_gan = 106.0;  {Elastic stiffness constant}
  c13_Aln = 108.0;
  c13_Inn = 92.0;
  c33_gan = 398.0;
  c33_Aln = 373.0;
  c33_Inn = 224.0;
   del_cr_gan = 0.019; {eV}
   del_cr_Aln = -0.164;
   del_cr_Inn = 0.041;
   del_so_gan = 0.014;    {eV}
   del_so_Aln = 0.019;
   del_so_Inn = 0.001;
   a1_gan  = -6.5; {interband deformation potential}
   a1_Aln  = -9.0;
   a1_Inn  = -3.5;
   d1_gan  = -3.0;  {deformation potential}
   d1_Aln  = -3.0;
   d1_Inn  = -3.0;
   d2_gan  = 3.6;
   d2_Aln  = 3.6;
   d2_Inn  = 3.6;
   d3_gan  = 8.82;
   d3_Aln  = 9.6;
   d3_Inn  = 8.82;
   d4_gan  = -4.41;
   d4_Aln  = -4.8;
   d4_Inn  = -4.41;
var
 Eg0 : real; {bandgap at epsilon=0}
 gay : real;
 del_1, del_2, del_3: real;
 Ec, a_1, a_c, P_ce, theta_e, lambda_e, E_1, E_2, E_3  : real;
 temp: real;
 a_f, a_s : real;
 aa, bb : real;
 av1, av2, av3, av4, av5 : real;
 epsilon_xx, epsilon_zz : real;
 d_1, d_2, d_3, d_4, del_cr, del_so : real;
 c13, c33: real;
begin
 gay := 1.0 - Alx - Iny;
 a_f := Alx*a0_Aln + Iny*a0_Inn + gay*a0_gan;
{ a_s := a0_gan;  }
 a_s := AlxSub*a0_Aln + InxSub*a0_Inn + (1.0-AlxSub-InxSub)*a0_gan;;
 epsilon_xx := (a_s - a_f)/a_f;
 c13 :=Alx*c13_Aln + Iny*c13_Inn + gay*c13_gan;
 c33 :=Alx*c33_Aln + Iny*c33_Inn + gay*c33_gan;
 epsilon_zz := - 2.0*epsilon_xx*c13/c33;
 Eg0 := Eg0_AlIngan(Alx, Iny);
 {crystal-field split energy}
 del_cr := Alx*del_cr_Aln + Iny*del_cr_Inn + gay*del_cr_gan;
 {Spin-orbit split-off energy}
 del_so := Alx*del_so_Aln + Iny*del_so_Inn + gay*del_so_gan;
 del_1 := del_cr;   {Eq. 13}
 del_2 :=  del_so/3.0; {Eq.13}
 del_3 := del_2; {Eq.13}
 {interband deformation potential}
 a_1 := Alx*a1_Aln + Iny*a1_Inn + gay*a1_gan;
 {conductio-band deformation potential}
 a_c := 0.5*a_1; {Table III}
 {a_c = a_cz = a_ct}
 {t: transverse to the c-axis; z: along to c-axis}
 {P_ce := a_cz*epsilion_zz + a_ct*(epsilon_xx + epsilon_yy}
 P_ce := a_c*(2.0*epsilon_xx + epsilon_zz);{hydrostatic energy shift}
 Ec := Eg0 + del_1 + del_2 + P_ce; {Eq.49}
 d_1 :=Alx*d1_Aln + Iny*d1_Inn + gay*d1_gan; {deformation potential}
 d_2 :=Alx*d2_Aln + Iny*d2_Inn + gay*d2_gan;
 d_3 :=Alx*d3_Aln + Iny*d3_Inn + gay*d3_gan;
 d_4 :=Alx*d4_Aln + Iny*d4_Inn + gay*d4_gan;
 theta_e := d_3*epsilon_zz + 2.0*d_4*epsilon_xx; {Eq.34}
 lambda_e :=d_1*epsilon_zz + 2.0*d_2*epsilon_xx; {Eq.34}
 E_1 := del_1 + del_2 + theta_e + lambda_e;  {Eq.47}
 calbandgap:= Ec - E_1;
end;

function polarization(Alx:real;Iny:real):real;
const
   a0_gan  =  3.189;  {a-lattice parameter}
   a0_Aln  =  3.112;
   a0_Inn = 3.545;
   c13_gan = 106.0;  {Elastic stiffness constant}
   c13_Aln = 108.0;
   c13_Inn = 92.0;
   c33_gan = 398.0;
   c33_Aln = 373.0;
   c33_Inn = 224.0;
   e33_gan =  1.27; {Piezoelectric constant}
   e33_Aln =  1.79;{c/m^2}
   e33_Inn = 0.97;
   e13_gan = -0.35;
   e13_Aln = -0.5;
   e13_Inn = -0.57;
   sp_gan  = -0.029;
   sp_Aln  = -0.081; {c/m^2 }
   sp_Inn = -0.032;
   PEpolFac = 1.0;
   SpolFac = 1.0;
var
  gay: real;
  a0_AlIngan : real;
  c13_AlIngan, c33_AlIngan : real;
  substrate : real;
  strain1, strain3, r_AlIngan : real;
  e13, e33, pz, sp : real;
begin
  gay := 1.0 - Alx - Iny;
  a0_AlIngan := Alx*a0_Aln + Iny*a0_Inn + gay*a0_gan;
  c13_AlIngan :=Alx*c13_Aln + Iny*c13_Inn + gay*c13_gan;
  c33_AlIngan :=Alx*c33_Aln + Iny*c33_Inn + gay*c33_gan;
  substrate := a0_gan;
  strain1 :=  substrate/a0_AlIngan - 1.0;
  r_AlIngan := 2.0*c13_AlIngan/c33_AlIngan;
  strain3 := -r_AlIngan*strain1;
  e33 := Alx*e33_Aln +Iny*e33_Inn + gay*e33_gan;
  e13 := Alx*e13_Aln + Iny*e13_Inn + gay*e13_gan;
  pz := e33*strain3 + 2.0*e13*strain1;
  sp := Alx*sp_Aln + Iny*sp_Inn + gay*sp_gan;
  polarization := PEpolFac*pz + SPolFac*sp;
end;

function dielecconst(Al,Iny: real):real;
const
   epsilon_gan =  8.9; {}
   epsilon_Aln =  8.5;
   epsilon_Inn = 15.3;
var
 ga : real;
begin
 ga := 1.0-Al-Iny;
 dielecconst := epsilon0*(ga*epsilon_gan
    + Al*epsilon_Aln + Iny*epsilon_Inn);
end;

procedure cplot(x:integer; yy:real; col:word);
var y : integer;
begin
     y:= Yoffset - round (yy / Yscale);
     if (y > 0) and (y <1000) then begin
         x := x div Xscale;
         PutPixel(x+Xoffset,y,col);
     end;
end;

procedure cline(x1:integer; yy1:real; x2:integer; yy2:real);
var y1, y2 : integer;
begin
  if (abs(yy1/Yscale) <2e3) and (abs(yy2/Yscale)<2e3) then begin
     y1:= Yoffset - round (yy1 / Yscale);
     y2:= Yoffset - round (yy2 / Yscale);
       x1 := x1 div Xscale;
       x2 := x2 div Xscale;
       line(x1+Xoffset,y1,x2+Xoffset,y2);
  end;
end;

procedure hgrXY(x,y:integer);
begin
   moveto(x*8,y*16)
end;

procedure setup;
var
  bandOffset,  Al, Indi : real;
  pdopingSt, pdopingEnd : real;
  ndopingWidth, pdopingWidth,
  ndopingSt, ndopingEnd, temp, channelthick, calt : real;
  z, n : integer;
begin
{setup parameters}
  thick[1] := 200.0; {Algan barrier}
  thick[2] := 10.0;  {Aln blocking barrier}
  thick[3] := 1200.0;
  channelthick := 0.5e4;
  Acceptorden  := 1.0e14; {4.0e17; {/cm3}}
  donorden     := 1.0e14; { 1.0e18; }{/cm3}
  acceptorden  := acceptorden/1.0e8; {/cm2/a}
  donorden     := donorden/1.0e8; { 1.0e18/1.0e8;} {/cm2/a}
  ndopingSt    := 0.0;       {ndoing start position}
  ndopingWidth := thick[1];  {ndoping width}
  ndopingEnd   := ndopingSt + ndopingWidth;
  pdopingSt    := thick[1]+thick[2]; {p-doping start}
  pdopingWidth := 1.0e3; {A}  {pdoping width}
  pdopingEnd   := pdopingSt+pdopingWidth;
  calt := pdopingEnd-thick[1]-thick[2];
  if thick[3] < calt then thick[3] := calt;
  thickbuff := channelthick-thick[3]; {buffer thickness - 2D channel thickness}
  dz := 1.0;  { step in angstrom }
  z1 := round(thick[1]/dz);
  z2 := z1 + round(thick[2]/dz);
  z3 := z2 + round(thick[3]/dz);
  if z3 > zm then begin
  repeat
    dz := dz + 1.0;
    z1 := round(thick[1]/dz);
    z2 := z1 + round(thick[2]/dz);
    z3 := z2 + round(thick[3]/dz);
  until z3 < zm
  end;
  Alz[1]   := 0.3;     { Al fraction }
  Alz[2]   := 0.53;
  Alz[3]   := 0.0;

  Inz[1]   := 0.0;
  Inz[2]   := 0.0;
  Inz[3]   := 0.0;

  AlxSub      := 0.0;
  InxSub       := 0.0;
  T_k        := 400.0;     { temperature }
  bandOffset := 0.;
  nMax := 1;
  fixedNMax := false;
  FPenergy   := 1.5e3; {meV} {Fermi level from the cb at top surface}
  Fermibuffer := 1.0e3; {meV} {Fermi level from the Vb at the buffer}
  {If a hole channel exists at the buffer interface, Fermibuffer is}
  {about zero or a negative number.}
  beac       := 300.0; {acceptor level above the Vb}
  bedon      := 100.0; {donor level below the cb}
  Vgs := 0.0;{ -4.0e3;}{gate voltage}
  Mw := 0.2;
  Mb := 0.2*(1.0-alz[1]) + 0.28*alz[1];
{end of setup parameters}


{list of fixed parameters}
  Fact1:=2.62468e-4 *dz*dz*Mw;
  Fact2:=2.62468e-4 *dz*dz*Mb;
  kT   := T_k*13.80648/1.60217657*1.0e-2; { temperature in meV  }

  for n := 1 to layer do begin
    al := alz[n];
    indi := Inz[n];
    bandgap[n] := 1e3*calbandgap(al,Indi);
    pol[n] := polarization (al,Indi);
    epsi[n] := dielecconst(al,Indi);
  end;
  for n := 1 to layer do Vh[n] := bandOffset*(bandgap[n]-bandgap[3]);

  for z := 1 to z3 do begin
    Rhoa[z] := 0.0;
    Rhod[z] := 0.0;
  end;
    zndop1 := round(ndopingSt/dz);
    zndop2 := round(ndopingEnd/dz);
    zpdop1 := round(pdopingSt/dz);
    zpdop2 := round(pdopingEnd/dz);
    if zpdop2 > z3 then zpdop2 := z3;
  if donorden > 1.0 then
    for z:= zndop1+1 to zndop2 do Rhod[z] := donorden*dz*1.0e-12;
  {}
  if acceptorden > 1.0 then
   for z := (zpdop1+1) to zpdop2 do Rhoa[z] := acceptorden*dz*1.0e-12; {}
end;

 procedure InitPotential(surfacefac,nelec:real);
 var
   dEfield: Larray;
   Vref : real;
   z, i : integer;
 begin
  sfcden := -SurfaceFac*pol[1]+ nelec*chrg/1.0e3;{surface induced charge.}
  for i := 1 to 3 do dEfield[i] :=1.0e5*(pol[i]+sfcden)/epsi[i];  {meV/a}
  for z := 1 to z1 do    V0[z] := dEfield[1]*z*dz;
  if z2 > z1 then
  for z := z1+1 to z2 do V0[z] := V0[z1] + dEfield[2]*(z-z1)*dz;
  if z3 > z2 then
  for z := z2+1 to z3 do V0[z] := V0[z2] + dEfield[3]*(z-z2)*dz;
  for z := 1 to z1 do    V0[z] := V0[z] + Vh[1];
  if z2 > z1 then
  for z := z1+1 to z2 do V0[z] := V0[z] + Vh[2];
  Vref := V0[z2+1];
  for z := 1 to z3 do    V0[z] := V0[z] - Vref;
    for z :=1 to z3 do begin
      V[z] := V0[z];
      Psi[z] := 0.0;
      phi[z] := 0.0;
    end;
    for i:=0 to nsubMax do begin
    { Energy[i]:=20.0*(i+1);  }
     sub_density[i]:=0.0;
    end;
    EFermi := 500.0;
    nMax := nmax-1;
end;

procedure FindZmaxZmin(E:real);
var
  WKb : real;
  z : integer;
begin
     z:=z2;
     WKb:=0.0;
     repeat
           z := z+1;
           if V[z] > E then WKb:=WKb +sqrt(Fact1*(V[z]-E));
     until (WKb > 7.0) or (z = z3-2 {z5-2});
     zmax:=z;
     z:=z2;
     WKb:=0.0;
     repeat
           z := z-1;
           if V[z] > E then WKb:=WKb +sqrt(Fact2*(V[z]-E))
           else WKb := 0;
     until (WKb > 7.0) or (z = 2);
     zmin:=z;
end;

procedure check_nodes( var nnodes:integer);
var z, sig,old_sig, z_bot, z_top : integer;
begin
     z_bot := zmin + 5;
     z_top := zmax - 5;
     nnodes:=0;
     if Psi[z_bot] > 0.0 then old_sig:= 1 else old_sig:=-1;
     for z := z_bot to z_top do begin
           if Psi[z] > 0.0 then sig:=1 else sig:=-1;
           if sig <> old_sig then begin
             nnodes:= nnodes + 1;
             old_sig:=sig;
           end
     end
end;

function fx2(E: real; nsub:integer):real;
const PsiMin = 1e-3;
var
  ratio : real;
  z, zm, zp : integer;
begin
   FindZmaxZmin(E);
   Psi[zmax+1]:=PsiMin;
   Psi[zmax] := PsiMin;
   for z:=zmax downto zmin+1 do begin
    zm := z-1;
    zp := z+1;
    Psi[zm] := ((2.0 + 5.0*(V[z]-E)*Fact1/6.0)*Psi[z]
                 - (1.0-Fact1*(V[zp]-E)/12.0)*Psi[zp])
                 /(1.0 - (V[zm] - E)*Fact1/12.0);
   end;
   ratio := Psi[zmin]/PsiMin;
   fx2 := ratio;
end;

procedure Subbands(surfacefac,nelec:real);
LabEL 99;
cOnST
   itmax = 100;
   eps = 1.0e-7;
   tol = 1.0e-6;
   del0 = 10.0;
VaR
   a, b, c, d, e: real;
   min1, min2, min: real;
   fa, fb, fc, p, q, r: real;
   s, tol1, xm: real;
   no, nodes, z, iter: integer;
   nsub : integer;
   sign, old_sign : integer;
   del, del1,sps : real;
bEgIn
  for nsub := 0 to nMax do begin
   del := del0;
   if nsub = 0 then a := energy[0]
   else
   a := Energy[nsub-1]+del/2.0;
   old_sign := 0;
   repeat
    fa := fx2(a, nsub);
    check_nodes(nodes);
    no := nodes - nsub;
    if no < 1 then sign := 1
    else if no >1 then sign := -1
    else sign := 0;
    if old_sign <> sign then begin
     del := del/1.9;
     old_sign := sign;
    end;
    a := a + del*sign;
   { if a >= V[1] then begin
      writeln('E : above the barrior');
      writeln (a:7:1,'  ',  V[1]:7:1);
      readln;
      Halt;
      end;   }
   until (no = 1);
   del := del0;
   if nsub = 0 then b := a/2.0
   else b := (Energy[nsub-1] + Energy[nsub])/2.0;
   if b > (a-del) then b := a - del;
   old_sign := 0;
   repeat
    fb := fx2(b, nsub);
    check_nodes(nodes);
    no := nodes - nsub;
    if no=1 then begin
     a:= b;
     fa := fb;
    end;
    if no < 0 then sign := 1
    else if no > 0 then sign := -1
    else sign := 0;
    if old_sign <> sign then  begin
     del := del/1.9;
     old_sign := sign;
   end;
   b := b + del*sign;
   until (no = 0);
   if fa*fb > 0.0 then begin
    writeln('fa*fb : positive; a:',a:7:2, '  b: ', b:7:2);
    writeln('fa:  ',fa:13, '  fb:  ',fb:13);
    writeln ('nsub : ', nsub:3);
    goto 99;
   end;
   fc := fb;
   FOR iter := 1 TO itmax dO bEgIn
      IF fb*fc > 0.0 THEn bEgIn
         c := a;
         fc := fa;
         d := b-a;
         e := d
      End;
      IF abs(fc) < abs(fb) THEn bEgIn
         a := b;
         b := c;
         c := a;
         fa := fb;
         fb := fc;
         fc := fa
      End;
      tol1 := 2.0*eps*abs(b)+0.5*tol;
      xm := 0.5*(c-b);
      IF (abs(xm) <= tol1) OR (fb = 0.0) THEn bEgIn
         Energy[nsub] := b;
         sps := 0.0;
         for z := zmin to zmax do sps := sps + sqr(Psi[z]);
         for z := 1 to z3 do PsiSq[nsub,z] := 0.0;
         if sps = 0.0 then
         begin
            writeln('sps is zero.');
            readln;
         end;
         for z := zmin to zmax do  PsiSq[nsub,z] := sqr(Psi[z])/sps;
         zfirst[nsub] := zmin;
         zlast[nsub] := zmax;
         gOTO 99
      End;
      IF (abs(e) >= tol1) and (abs(fa) > abs(fb)) THEn bEgIn
         s := fb/fa;
         IF a = c THEn bEgIn
            p := 2.0*xm*s;
            q := 1.0-s
         End
         ELSE bEgIn
            q := fa/fc;
            r := fb/fc;
            p := s*(2.0*xm*q*(q-r)-(b-a)*(r-1.0));
            q := (q-1.0)*(r-1.0)*(s-1.0)
         End;
         IF p > 0.0 THEn q := -q;
         p := abs(p);
         min1 := 3.0*xm*q-abs(tol1*q);
         min2 := abs(e*q);
         IF min1 < min2 THEn min := min1 ELSE min := min2;
         IF 2.0*p < min THEn bEgIn
            e := d;
            d := p/q
         End
         ELSE bEgIn
            d := xm;
            e := d
         End
      End
      ELSE bEgIn
         d := xm;
         e := d
      End;
      a := b;
      fa := fb;
      IF abs(d) > tol1 THEn b := b+d
      ELSE bEgIn
         IF xm >= 0 THEn b := b+abs(tol1)
         ELSE b := b-abs(tol1)
      End;
      fb := fx2(b, nsub)
   End;
  99:
  end;
End;

function Fermi_density(EFermi: real): real;
var nsub : integer;
    density, temp, temp2, Mww, sden : real;
begin
Mww := Mw*0.4178;
density:=0.0;
nsub:=0;
repeat
   temp := EFermi - Energy[nsub];
   if T_k < 0.5 then
   begin
      if temp > 0.0 then sden:=temp*Mww
      else sden:= 0.0;
   end
   else begin
      temp2 := temp/kT;
      if temp2 < 60.0 then sden:= Mww*kT*ln(1.0+exp(temp2))
      else sden:=temp*Mww;
   end;
   density:= density + sden;
   Sub_density[nsub] := sden;
   nsub:=nsub+1;
until nsub > nMax;

Fermi_density := density;
end;


procedure Fermi_Energy(nelec:real);   { newton Interpolation }
var
  density2,density1, e1, e2, dE  :real;
begin
  dE :=1.0;
  e1 := Efermi;
  density1:=Fermi_density(e1);
  repeat
   e2 := e1 + dE;
   density2:=Fermi_density(e2);
   e1:=e1+dE*(nelec-density1)/(density2-density1);
   density1 := Fermi_density (e1);
  until abs(density1-nelec) < 1e-5;
  Efermi := e1;
end;

procedure calPotential(a, surfacefac, nelec:real);
var
  z,i : integer;
  Vold : ^Varray;
  Vref, temp, facceptor, fdonor: real;
begin
  new(Vold);
  Fermi_Energy(nelec);
  ionaden := 0.0;
  iondden := 0.0;
  eden := 0.0;
  for z:=1 to z3 do begin
   Vold^[z]:=V[z];
   Phi[z]:=0;
   for i:=0 to nMax do
      Phi[z]:=Phi[z] + PsiSq[i,z]*Sub_density[i];

   if kT > 1e-10 then  begin
       temp :=(V[z]-bedon - Efermi)/kT;
       if temp > 30.0 then fdonor := 1.0
       else if temp < -30.0 then fdonor := 0.0
       else fdonor :=1.0 - 1.0/(1.0+exp(temp)/2.0);
   end
   else begin
       if (V[z]-bedon-Efermi)>0.0 then fdonor := 1.0 else fdonor := 0.0;
   end;
   if kT > 1e-10 then begin
       temp :=(V[z]-bandgap[3] + beac - Efermi)/kT;
       if temp > 30.0 then facceptor := 0.0
       else if temp <-30.0 then facceptor := 1.0
       else facceptor :=1.0/(1.0+ 4.0*exp(temp));
   end
   else begin
       if (V[z]-bandgap[3] + beac - Efermi) < 0.0 then
          facceptor := 1.0 else facceptor := 0.0;
   end;
   eden := eden + phi[z];
   Phi[z] := Phi[z] + facceptor*Rhoa[z] - fdonor*Rhod[z];  {e12/cm2}
   ionaden := ionaden +  facceptor*Rhoa[z]; {positive}
   iondden := iondden + fdonor*Rhod[z];     {positive}
  end;
  sfcden := -SurfaceFac*pol[1]+nelec*chrg/1.0e3;{surface induced charge.}
  chrgden := eden+ionaden-iondden;
  backden := -sfcden + chrgden*chrg/1.0e3;;
  freechrg := -eden*chrg/1.0e3;
  iaden:= -ionaden*chrg/1.0e3;    {negative}
  idden:= iondden*chrg/1.0e3;
  dVSq:=0.0;
 { a:= 0.4; }
  V[0] :=0.0;
  V[1]:=0.0;
  for z:=1 to z3-1 do
       V[z+1]:= Phi[z-1]+10.0*Phi[z]+Phi[z+1] + 2.0*V[z] - V[z-1];
  for z := 1 to z3 do V[z] := -1.0e2*chrg*dz*V[z]/12.0/epsi[3] + V0[z];
  Vref := V[z2+1];
  for z:=1 to z3 do begin
    V[z]:=V[z] - Vref;
    dVSq := dVSq + sqr(V[z]-Vold^[z]);
    V[z] := a*V[z] + (1.0-a)*Vold^[z];
  end;
  Vref := V[z2+1];
  for z:=1 to z3 do V[z]:=V[z] - Vref;
  dVSq := sqrt(dVSq/z3);
  if Sub_density[nMax] > 1.0e-6 then begin
     if not fixedNMax then nMax := nMax+1;
     if nMax > nsubMax then nMax := nsubMax;
  end
  else begin
    if  Sub_density[nMax-1] < 1.0e-6 then nMax := nMax-1;
  end;

  dispose(Vold);
end;

procedure cal (x, y:real; var delV, FermiPin: real; var iter:integer);
var a, sf,ne : real;

begin
  sf := x;
  ne := y;
  InitPotential(sf,ne);
  iter := 0;
  a := 0.6;
  repeat
      inc(iter);
      Subbands(sf,ne);
      calPotential(a, sf,ne);
      if dVSq > 1e-4 then a:= 0.5
      else if dVSq > 1e-5 then a := 0.3
      else a := 0.1;
  until (dVSq < 1.0e-6) or (iter > 60);
  Vsub := V[z3] + (V[z3]-V[z3-1])/dz*thickbuff;
  delV := Vsub - bandgap[3] +Fermibuffer - Efermi; {for intrinsic subs.}
  FermiPin := V[1] -FPenergy - Efermi +Vgs;
end;


procedure plotPotential;
var
   z : integer;
begin
  for z := 1 to z3 do cplot(z,V[z], white);
end;

procedure plotResults;
var
   z, nsub, y1, y2, zt, i : integer;
   s1,s2,s3, s4, s5: string[9];
begin
   xexp := 0.0;
   for z:=1 to z3 do begin
     Phi[z]:=0;
     for i:=0 to nMax do Phi[z]:=Phi[z] + PsiSq[i,z]*Sub_density[i];
     xexp := xexp + z*Phi[z];
   end;
   if nelec > 1e-20 then xexp := dz*xexp/nelec;
  hgrXY(3,3);
  OutText(' nsub En(meV) n_e(e12/cm2) zmin(a) zmax(a)');
  for nsub := 0 to nMax do begin
   Str(nsub:3,s1); Str(Energy[nsub]:8:2,s2); Str(Sub_density[nsub]:8:5,s3);
   Str(zfirst[nsub]*dz:8:1,s4);  Str(zlast[nsub]*dz:8:1,s5);
   hgrXY(3, 4+nsub); OutText(' '+s1+' '+s2+' '+s3+' '+s4+' '+s5);
  end;

  hgrXY(3,8+nMax); Str(Efermi:9:2,s1); OutText('EFermi (meV)        : '+s1);
  hgrXY(3,9+nMax); Str(xexp:9:2,s1);   OutText('<x> (a)             :'+s1);

  hgrXY(3,10+nMax); Str(SurfaceFac:9:7,s1); OutText('Surface factor      : '+s1);
  hgrXY(3,11+nMax);Str(V[1]:9:2,s1); Str(V[1]-bandgap[1]:9:2,s2);
  OutText('Surf. Vc (meV)      : '+s1+ '   Vv : '+s2);
  hgrXY(3,12+nMax);Str(Vsub:9:2,s1);  Str(Vsub-bandgap[3]:9:2,s2);
  OutText('Subs. Vc (meV)      : '+s1+ '   Vv : '+s2);
  hgrXY(3,13+nMax);Str(dz:5:2,s1); OutText('dz(ang)        : '+s1);

  sfcden := -SurfaceFac*pol[1]+nelec*chrg/1.0e3;{surface induced charge.}
  chrgden := eden+ionaden-iondden;
  freechrg := -eden*chrg/1.0e3;
  iaden:= -ionaden*chrg/1.0e3;    {negative}
  backden := -sfcden + chrgden*chrg/1.0e3;;
  idden:= iondden*chrg/1.0e3;

  hgrXY(3,14+nMax);Str(sfcden:9:5,s1);
  OutText('Surf. cd(c/m2): '+s1);

  Str(freechrg:9:5,s1);
  hgrXY(3,15+nMax);Str(eden:9:5,s2);
  OutText('elec den. (e12/cm2): '+s1+'  '+s2);

  hgrXY(3,16+nMax);Str(iaden:9:5,s1);  Str(ionaden:9:5,s2);
  OutText('ion ac cd (c/m2)(e12/cm2): '+s1+'  '+s2);

  hgrXY(3,17+nMax);Str(iondden:9:5,s2); Str(idden:9:5,s1);
  OutText('ion donor cd. (c/m2)(e12/cm2): '+s1+'  '+s2);

  hgrXY(3,20+nMax);Str(backden:9:5,s1);
  OutText('Rear Surf. cd(c/m2): '+s1);



  if donorden > 1e-10 then
   for z := zndop1+1 to zndop2 do cplot(z,V[z]-bedon, yellow);
  for z := 1 to z1 do cplot(z,V[z]-bandgap[1], white);
  if z2 > z1 then
  for z := z1+1 to z2 do cplot(z,V[z]-bandgap[2], white);
  if z3 > z2 then
  for z := z2+1 to z3 do cplot(z,V[z]-bandgap[3], white);


  if zpdop2 > zpdop1 then
  begin
  if acceptorden > 1.0e-10 then
   for z := zpdop1+1 to zpdop2 do cplot(z,V[z]-bandgap[3] + beac, blue);
  end;

  y1 := round(V[1]-bandgap[1]);
  y2 := round(V[1]);
  for z := y1 to y2 do cplot(0, 1.0*z, white);


  y1 := round(V[z1-1]);
  y2 := round(V[z1+1]);
  if y1 > y2 then
  for z := y1 downto y2 do cplot(z1, 1.0*z, white)
  else  for z := y1 to y2 do cplot(z1, 1.0*z, white);

  y1 := round(V[z2-1]);
  y2 := round(V[z2+1]);
  if y1 > y2 then
  for z := y1 downto y2 do cplot(z2, 1.0*z, white)
  else  for z := y1 to y2 do cplot(z2, 1.0*z, white);
  for nsub :=0 to nMax do begin
      zmin := zfirst[nsub];
      zmax := zlast[nsub];
      for z:=zmin to zmax do begin
        cplot(z,Energy[nsub], yellow);
        cplot(z, 1e4*PsiSq[nsub,z] + Energy[nsub], green);
      end;
   end;
  z:=1;
  zt := z3;
  repeat
         cplot(z,EFermi, red);
         z := z + 4
  until z > zt;
end;

procedure newtonInterPol;

var x0, x1,x2, dx, dy, delV0, delV1, delV2, delv3,
    FermiPin1, FermiPin0, FermiPin2, fermipin3,
    y0, y1,y2, tobezero : real;
    iter,iter1, i : integer;
begin
  writeln ('x0      y0    delV0   FermiPin0  dVSq tobezero iter1');

  nelec := 1.0;
  SurfaceFac := 0.55;
  x0 := SurfaceFac;
  y0 := nelec;
  dx := 0.001;
  dy := nelec/2.0;
for i := 1 to 4 do
begin
  cal(x0, y0, delV0, FermiPin0,iter1);
  writeln(x0:10:5, y0:10:5, delV0:13:5,FermiPin0:13:5);
  if delV0 > 0.0 then x1 := x0 + dx else x1:= x0 - dx;
  if fermipin0 > 0.0 then y1 := y0 + dy else y1:= y0 - dy;

  cal(x1, y0, delV1, FermiPin1,iter1);
  writeln(x1:10:5, y0:10:5, delV1:13:5,FermiPin1:13:5);

  x2 := x0 - 0.9*(x0-x1)*delV0/(delv0-delv1);
  cal(x2, y0, delV2, FermiPin2,iter1);
  writeln(x2:10:5, y0:10:5, delV2:13:5,FermiPin2:13:5);

  cal(x2, y1, delV3, FermiPin3,iter1);
  writeln(x2:10:5, y1:10:5, delV3:13:5,FermiPin3:13:5);

  y2 := y0 - (y0 - y1)*fermipin2/(fermipin2-fermipin3);
  cal(x2, y2, delV3, FermiPin3,iter1);
  writeln(x2:10:5, y2:10:5, delV3:13:5,FermiPin3:13:5);
   tobezero := abs(delV3)+abs(FermiPin3);
   writeln (x2:11:9,' ',y2:11:8,' ',delV2:11:4,' ',FermiPin3:11:4,' ',
         dVSq*1e6:7:2,' ',tobezero:13,' ',iter1:2,' ',iter:3);
  x0 := x2;
  y0 := y2;
  dx := dx/10.0;
  dy := dy/10.0;
 end;
  cal(x0, y0, delV0, FermiPin0,iter1);
  writeln(x0:10:5, y0:10:5, delV0:13:5,FermiPin0:13:5);
  if delV0 > 0.0 then x1 := x0 + dx else x1:= x0 - dx;
  if fermipin0 > 0.0 then y1 := y0 + dy else y1:= y0 - dy;

  cal(x1, y0, delV1, FermiPin1,iter1);
  writeln(x1:10:5, y0:10:5, delV1:13:5,FermiPin1:13:5);

  x2 := x0 - 1.0*(x0-x1)*delV0/(delv0-delv1);
  cal(x2, y0, delV2, FermiPin2,iter1);
  writeln(x2:10:5, y0:10:5, delV2:13:5,FermiPin2:13:5);

  cal(x2, y1, delV3, FermiPin3,iter1);
  writeln(x2:10:5, y1:10:5, delV3:13:5,FermiPin3:13:5);

  y2 := y0 - (y0 - y1)*fermipin2/(fermipin2-fermipin3);
  cal(x2, y2, delV3, FermiPin3,iter1);
  writeln(x2:10:5, y2:10:5, delV3:13:5,FermiPin3:13:5);
   tobezero := abs(delV3)+abs(FermiPin3);
   writeln (x2:11:9,' ',y2:11:8,' ',delV2:11:4,' ',FermiPin3:11:4,' ',
         dVSq*1e6:7:2,' ',tobezero:13,' ',iter1:2,' ',iter:3);

  surfacefac := x2;
  nelec := y2;
end;



procedure SaveResults;
var z, i : integer;
    FermiPinSubs, FermiPinSurf: real;
    OutFile : text;
begin
   assign (OutFile, 'gan00.txt');
   Rewrite (OutFile);
   for z:=1 to z3 do begin
     write(OutFile, z*dz:7:1,' ', V[z]:8:2,' ',1e2*phi[z]/dz:7:5);
     for i:=0 to nMax-1 do write(OutFile,' ', 1e4*PsiSq[i,z]:7:3);
     writeln(OutFile,' ',1e4*PsiSq[nMax,z]:7:3);
   end;
   FermiPinSubs := Vsub-Efermi;
   FermiPinSurf := V[1] - Efermi;
   writeln (OutFile, 'Efermi(meV)      : ', EFermi:7:2);
   writeln (OutFile, 'V[z4]-Efermi(meV): ', FermiPinSubs:7:1);
   writeln (OutFile, 'V[1]-EFermi(meV) : ', FermiPinSurf:7:1);
   writeln (OutFile, 'x_expect(a)      : ', xexp:7:2);
   writeln (OutFile, 'nelec(e12cm-2)   : ', nelec:7:5);
   writeln (OutFile, 'SurfaceFac       : ', SurfaceFac:7:5);
   writeln (OutFile, 'Surf-charge(c/m2): ', sfcden:13);
   for i := 0 to nMax do
    writeln (OutFile, i:3,' ',Energy[i]:7:2,' ',Sub_density[i]:7:5);
   close (OutFile);
end;

{ main routine }
begin
  setup;
  newtonInterPol;
  Inigraph;
  plotpotential;
  plotResults;
  readln;
  closegraph;
{  SaveResults;}
end.
