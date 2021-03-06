program ganhemt103;
uses dos, crt, graph;
const
   zm       = 5000; { total number of pixels }
   layer    = 3;
   nsubmax  = 15;   { maximum number of subbands considered in this program }
   chrg     = 1.602177; { unit charge }
   epsilon0 = 8.85418;
   minnelec = 1.0e-7;
type
  varray    = array[0..zm] of real;
  larray    = array[1..layer] of real;
  earray    = array[0..nsubmax] of real;
  psiarray  = array[0..nsubmax,0..zm] of real;
  zarray    = array[0..nsubmax] of integer;
  real2     = extended;
var
  z0,z1,z2,z3,za, zmax, zmin, nmax : integer;
  t_k, kt, vgs, dz, wkb1, wkb2, fact1, fact2,sf,ne:real;
  donorden,acceptorden,ionaden, iondden, e_fermi : real;
  fermisurf,fermibuffer, channelthick : real;
  alxsub, inxsub, mw, mb, thickbuff, beac, bedon : real;
  alz, inz, pol, epsi, bandgap, vh, thick: larray;
  v0, v, psi, phi, rhoa, rhod, vold : varray;
  energy, sub_density : earray;
  zfirst,zlast: zarray;
  psisq, psi0 :psiarray;
  fixednmax: boolean;
  outfile: text;

function abc (x, g_ac, g_bc, bowing : real): real;
var y, g : real;
begin
  y := 1.0-x;
  g := y*g_ac + x*g_bc - x*y*bowing;
  abc := g;
end;

function eg0_alingan(al,iny:real):real;
const
  gan0_g   = 3.507; {ev, t = 0k}
  aln0_g   = 6.23; {ev, t = 0k}
  inn0_g   = 1.4; {1.994;} {ev, should be corrected}
var
 u, v, w, ga, gan_g, aln_g, inn_g : real;
 gan, aln, inn , bow_algan, bow_alinn, bow_gainn : real;
 gaal, alin, gain, temp, deno: real;
 alpha_gan, beta_gan : real;
 alpha_aln, beta_aln : real;
 alpha_inn, beta_inn : real;
begin
 ga := 1.0 - al - iny;
 bow_algan := 1.0;  {0.44 : by voznyy et al. semicond. v.38, p.316 (04)}
 bow_alinn := 4.16; {calculated by voznyy et al.}
 bow_gainn := 1.43; {ager iii et al. proc. of spie v.5530, p.308}
             {2.72 : voznyy et al.}
 alpha_gan := 0.909; {mev/k}
 beta_gan := 830.0; {k}
 gan_g := gan0_g - 1.0e-3*alpha_gan*sqr(t_k)/(t_k + beta_gan);
 alpha_aln := 1.799; {mev/k}
 beta_aln := 1462.0; {k}
 aln_g := aln0_g - 1.0e-3*alpha_aln*sqr(t_k)/(t_k + beta_aln);
 alpha_inn := 0.245; {mev/k}
 beta_inn := 624.0; {k}
 inn_g := inn0_g - 1.0e-3*alpha_inn*sqr(t_k)/(t_k + beta_inn);
 if ga < 1e-2 then
  temp := al*aln_g + iny*inn_g - al*iny*bow_alinn
 else begin
  if iny < 1e-2 then
   temp := ga*gan_g + al*aln_g - ga*al*bow_algan
  else begin
   if al < 1e-2 then
     temp := ga*gan_g + iny*inn_g - ga*iny*bow_gainn
   else begin
    deno := ga*al +al*iny + iny*ga;
    u := (1.0 - ga + al)/2.0;
    v := (1.0 - al + iny)/2.0;
    w := (1.0 - iny + ga)/2.0;
    gan := gan_g;
    aln := aln_g;
    inn := inn_g;
    gaal := abc(u, gan, aln, bow_algan);
    alin := abc(v, aln, inn, bow_alinn);
    gain := abc(w, inn, gan, bow_gainn);
    temp := (ga*al*gaal + al*iny*alin + iny*ga*gain)/deno;
   end
  end
 end;
 eg0_alingan := temp;
end;

function calbandgap(alx,iny:real):real;
const
  a0_gan  =  3.189;  {a-lattice parameter}
  a0_aln  =  3.112;
  a0_inn = 3.545;
  c13_gan = 106.0;  {elastic stiffness constant}
  c13_aln = 108.0;
  c13_inn = 92.0;
  c33_gan = 398.0;
  c33_aln = 373.0;
  c33_inn = 224.0;
   del_cr_gan = 0.019; {ev}
   del_cr_aln = -0.164;
   del_cr_inn = 0.041;
   del_so_gan = 0.014;    {ev}
   del_so_aln = 0.019;
   del_so_inn = 0.001;
   a1_gan  = -6.5; {interband deformation potential}
   a1_aln  = -9.0;
   a1_inn  = -3.5;
   d1_gan  = -3.0;  {deformation potential}
   d1_aln  = -3.0;
   d1_inn  = -3.0;
   d2_gan  = 3.6;
   d2_aln  = 3.6;
   d2_inn  = 3.6;
   d3_gan  = 8.82;
   d3_aln  = 9.6;
   d3_inn  = 8.82;
   d4_gan  = -4.41;
   d4_aln  = -4.8;
   d4_inn  = -4.41;
var
 eg0 : real; {bandgap at epsilon=0}
 gay, del_1, del_2: real;
 ec, a_1, a_c, p_ce, theta_e, lambda_e, e_1 : real;
 a_f, a_s, epsilon_xx, epsilon_zz : real;
 d_1, d_2, d_3, d_4, del_cr, del_so : real;
 c13, c33: real;
begin
 gay := 1.0 - alx - iny;
 a_f := alx*a0_aln + iny*a0_inn + gay*a0_gan;
 a_s := alxsub*a0_aln + inxsub*a0_inn + (1.0-alxsub-inxsub)*a0_gan;;
 epsilon_xx := (a_s - a_f)/a_f;
 c13 :=alx*c13_aln + iny*c13_inn + gay*c13_gan;
 c33 :=alx*c33_aln + iny*c33_inn + gay*c33_gan;
 epsilon_zz := - 2.0*epsilon_xx*c13/c33;
 eg0 := eg0_alingan(alx, iny);
 {crystal-field split energy}
 del_cr := alx*del_cr_aln + iny*del_cr_inn + gay*del_cr_gan;
 {spin-orbit split-off energy}
 del_so := alx*del_so_aln + iny*del_so_inn + gay*del_so_gan;
 del_1 := del_cr;   {eq. 13}
 del_2 :=  del_so/3.0; {eq.13}
 {del_3 := del_2; }{eq.13}
 {interband deformation potential}
 a_1 := alx*a1_aln + iny*a1_inn + gay*a1_gan;
 {conductio-band deformation potential}
 a_c := 0.5*a_1; {table iii}
 {a_c = a_cz = a_ct}
 {t: transverse to the c-axis; z: along to c-axis}
 {p_ce := a_cz*epsilion_zz + a_ct*(epsilon_xx + epsilon_yy}
 p_ce := a_c*(2.0*epsilon_xx + epsilon_zz);{hydrostatic energy shift}
 ec := eg0 + del_1 + del_2 + p_ce; {eq.49}
 d_1 :=alx*d1_aln + iny*d1_inn + gay*d1_gan; {deformation potential}
 d_2 :=alx*d2_aln + iny*d2_inn + gay*d2_gan;
 d_3 :=alx*d3_aln + iny*d3_inn + gay*d3_gan;
 d_4 :=alx*d4_aln + iny*d4_inn + gay*d4_gan;
 theta_e := d_3*epsilon_zz + 2.0*d_4*epsilon_xx; {eq.34}
 lambda_e :=d_1*epsilon_zz + 2.0*d_2*epsilon_xx; {eq.34}
 e_1 := del_1 + del_2 + theta_e + lambda_e;  {eq.47}
 calbandgap:= ec - e_1;
end;

function polarization(alx:real;iny:real):real;
const
   a0_gan  =  3.189;  {a-lattice parameter}
   a0_aln  =  3.112;
   a0_inn = 3.545;
   c13_gan = 106.0;  {elastic stiffness constant}
   c13_aln = 108.0;
   c13_inn = 92.0;
   c33_gan = 398.0;
   c33_aln = 373.0;
   c33_inn = 224.0;
   e33_gan =  1.27; {piezoelectric constant}
   e33_aln =  1.79;{c/m^2}
   e33_inn = 0.97;
   e13_gan = -0.35;
   e13_aln = -0.5;
   e13_inn = -0.57;
   sp_gan  = -0.029;
   sp_aln  = -0.081; {c/m^2 }
   sp_inn = -0.032;
   pepolfac = 1.0;
   spolfac = 1.0;
var
  gay, a0_alingan : real;
  c13_alingan, c33_alingan : real;
  substrate, strain1, strain3, r_alingan : real;
  e13, e33, pz, sp : real;
begin
  gay := 1.0 - alx - iny;
  a0_alingan := alx*a0_aln + iny*a0_inn + gay*a0_gan;
  c13_alingan :=alx*c13_aln + iny*c13_inn + gay*c13_gan;
  c33_alingan :=alx*c33_aln + iny*c33_inn + gay*c33_gan;
  substrate := a0_gan;
  strain1 :=  substrate/a0_alingan - 1.0;
  r_alingan := 2.0*c13_alingan/c33_alingan;
  strain3 := -r_alingan*strain1;
  e33 := alx*e33_aln +iny*e33_inn + gay*e33_gan;
  e13 := alx*e13_aln + iny*e13_inn + gay*e13_gan;
  pz := e33*strain3 + 2.0*e13*strain1;
  sp := alx*sp_aln + iny*sp_inn + gay*sp_gan;
  polarization := pepolfac*pz + spolfac*sp;
end;

function dielecconst(al,iny: real):real;
const
   epsilon_gan =  8.9;
   epsilon_aln =  8.5;
   epsilon_inn = 15.3;
var
 ga : real;
begin
 ga := 1.0-al-iny;
 dielecconst := epsilon0*(ga*epsilon_gan
    + al*epsilon_aln + iny*epsilon_inn);
end;


procedure findzmaxzmin(e:real);
var
  wkb : real;
  z : integer;
begin
     z:=z2;
     wkb:=0.0;
     repeat
           z := z+1;
           if v[z] > e then wkb:=wkb +sqrt((v[z]-e));
     until (wkb > wkb1) or (z = z3-2 {z5-2});
     zmax:=z+1;
     z:=z2;
     wkb:=0.0;
     repeat
           z := z-1;
           if v[z] > e then wkb:=wkb +sqrt((v[z]-e))
           else wkb := 0;
     until (wkb > wkb2) or (z = z0+2);
     zmin:=z-1;
end;

procedure check_nodes( var nnodes:integer);
var z, sig,old_sig, z_bot, z_top : integer;
begin
     z_bot := zmin + 5;
     z_top := zmax - 5;
     nnodes:=0;
     old_sig:= 1;
     z := z_top;
     repeat
         if psi[z] > 0.0 then sig:=1 else sig:=-1;
         if sig <> old_sig then begin
             nnodes:= nnodes + 1;
             old_sig:=sig;
         end;
         z := z - 3;
     until z < z_bot;
end;

function fx2(e: real):real;
const psimin = 1e-3;
var
  ratio : real;
  z, zm, zp : integer;
begin
   findzmaxzmin(e);
   psi[zmax+1]:=0.85*psimin;
   psi[zmax] := psimin;
   for z:=zmax downto zmin+1 do begin
    zm := z-1;
    zp := z+1;
    psi[zm] := ((2.0 + 5.0*(v[z]-e)*fact1/6.0)*psi[z]
                 - (1.0-fact1*(v[zp]-e)/12.0)*psi[zp])
                 /(1.0 - (v[zm] - e)*fact1/12.0);
   end;
   ratio := psi[zmin]/psimin;
   fx2 := ratio;
end;


function fermi_density(efermi: real): real;
var nsub : integer;
    density, temp, temp2, mww, sden : real;
begin
mww := mw*0.4178;
density:=0.0;
nsub:=0;
repeat
   temp := efermi - energy[nsub];
   if t_k < 0.5 then
   begin
      if temp > 0.0 then sden:=temp*mww
      else sden:= 0.0;
   end
   else begin
      temp2 := temp/kt;
      if temp2 < 60.0 then sden:= mww*kt*ln(1.0+exp(temp2))
      else sden:=temp*mww;
   end;
   density:= density + sden;
   sub_density[nsub] := sden;
   nsub:=nsub+1;
until nsub > nmax;
fermi_density := density;
end;


procedure fermi_energy(nelec:real; var efermi:real);   { newton interpolation }
var
  density2,density1, e1, e2, de  :real;
begin
  de :=1.0;
 { if first then e1 := energy[0]
  else} e1:= efermi;
  density1:=fermi_density(e1);
  repeat
   e2 := e1 + de;
   density2:=fermi_density(e2);
   e1:=e1+de*(nelec-density1)/(density2-density1);
   density1 := fermi_density (e1);
  until abs(density1-nelec) < minnelec;
  efermi := e1;
end;

procedure calpotential( efermi:real; okay:boolean; var dvsq:real);
var
  z,i : integer;
  a: real;
  vref, temp, facceptor, fdonor: real2;
begin
  ionaden := 0.0;
  iondden := 0.0;
  for z:=z0 to z3 do begin
   phi[z]:=0;
   for i:=0 to nmax do
      phi[z]:=phi[z] + psisq[i,z]*sub_density[i];
   if kt > 1e-10 then  begin
       temp :=(v[z]-bedon - efermi)/kt;
       if temp > 30.0 then fdonor := 1.0
       else if temp < -30.0 then fdonor := 0.0
       else fdonor :=1.0 - 1.0/(1.0+exp(temp)/2.0);
   end
   else begin
       if (v[z]-bedon-efermi)>0.0 then fdonor := 1.0 else fdonor := 0.0;
   end;
   if kt > 1e-10 then begin
       temp :=(v[z]-bandgap[3] + beac - efermi)/kt;
       if temp > 30.0 then facceptor := 0.0
       else if temp <-30.0 then facceptor := 1.0
       else facceptor :=1.0/(1.0+ 4.0*exp(temp));
   end
   else begin
       if (v[z]-bandgap[3] + beac - efermi) < 0.0 then
          facceptor := 1.0 else facceptor := 0.0;
   end;
   phi[z] := phi[z] + facceptor*rhoa[z] - fdonor*rhod[z];  {e12/cm2}
   ionaden := ionaden +  facceptor*rhoa[z]; {positive}
   iondden := iondden + fdonor*rhod[z];     {positive}
  end;
  for z:=z0 to z3 do vold[z] := v[z];
  dvsq:=0.0;
  v[z0] :=0.0;
  v[z0+1]:=0.0;
  for z:=z0+1 to z3-1 do
       v[z+1]:= phi[z-1]+10.0*phi[z]+phi[z+1] + 2.0*v[z]- v[z-1];
  for z := z0 to z3 do  v[z] := -1.0e2*chrg*dz*v[z]/12.0/epsi[3] + v0[z];
  vref := v[z2+1];
  if okay then a := 0.3 else a:= 1.0;
  for z:=z0 to z3 do begin
    v[z]:=v[z] - vref;
    dvsq := dvsq + sqr (v[z]-vold[z]);
    v[z] := a*v[z] + (1.0-a)*vold[z];
  end;
  vref := v[z2+1];
  for z:=z0 to z3 do v[z]:=v[z] - vref;
  dvsq := sqrt(dvsq/(z3-z0));
  if sub_density[nmax] > minnelec then
  begin
     if not fixednmax then nmax := nmax+1;
     if nmax > nsubmax then nmax := nsubmax;
  end ;
end;

procedure set_design (var sf,ne,e_fermi:real);
var
   al, indi, bandoffset : real;
   z, n : integer;
begin
{setup parameters}
  thick[1] := 250.0;     {front barrier thickness in A}
  thick[2] := 0.0;       {second barrier thickness in A}
  channelthick := 1.5e4; {electron channel thickness in A}
  acceptorden  := 0.0e15;{acceptor doping density  /cm3}
  donorden     := 0.0e14;{doner doping density in /cm3}
  alz[1]   := 0.05;      {al fraction of the front barrier layer}
  alz[2]   := alz[1];    {al fraction of the second barrier layer}
  alz[3]   := 0.0;       {al fraction of the electron channel layer}
  inz[1]   := 0.0;       {In fraction of the front barrier layer}
  inz[2]   := 0.0;       {In fraction of the second barrier layer}
  inz[3]   := 0.0;      {In fraction of the electron channel layer}
  bandoffset := 0.7;     {conduction-band offset of GaN/AlGaN interface}
  alxsub      := 0.0;    {al fraction of the substrate layer}
  inxsub       := 0.0;   {In fraction of the substrate layer}
  beac       := 300.0;   {acceptor level above the valence band}
  bedon      := 100.0;   {donor level below the conduction band}
  acceptorden:= acceptorden/1.0e8; {acceptor density in /cm2/a}
  donorden   := donorden/1.0e8;    {donor density in /cm2/a}
  thick[3] := 4000.0;              {electron channel thickness covered by csl.}
  thickbuff:= channelthick-thick[3];{thickness of buffer treated approximately}
  if thickbuff < 0.0 then
  begin
  thickbuff := 0.0;
  thick[3] := channelthick;
  end;
  dz := 1.0;                       {step in angstrom }
  z2 := 300;                       {location of interface of 2d electrons}
  z1 := z2 - round(thick[2]/dz);   {location of interface of two barriers}
  z0 := z1- round(thick[1]/dz);    {location of interface of vac.and f.barrier}
  z3 := z2 + round(thick[3]/dz);   {terminal location of the self-consist. cal.}
  za := z2 + round(thick[3]/dz);   {acceptor doping terminal position}
  if za > zm then za := zm;
  if z0<0 then writeln(' z0 must be positive');
  t_k  := 310.0;                   {temperature }
  writeln ('layer al comp. indi comp. bandgap(mev) pol(c/m2), die.const');
  for n := 1 to layer do begin
    al := alz[n];
    indi := inz[n];
    bandgap[n] := 1e3*calbandgap(al,indi);
    pol[n] := polarization (al,indi);
    epsi[n] := dielecconst(al,indi);
    writeln (n:3, al:9:3, indi:9:3, bandgap[n]:12:2, pol[n]:12:6,
    epsi[n]/epsilon0:10:5);
  end;

  nmax := 0;             {maximum of subband occuping electrons}
  energy[0] := 20.0;     {first guess of the lowest energy in the beginning}
  e_fermi := energy[0];  {first guess of the fermid energy in the beginning}
  for n := 1 to nsubmax do energy[n]:= n*1.0e3; {initialization of other states}
  fixednmax := false;    {fixed subband numbers}
  fermisurf   := 1.0e3; {mev} {fermi level from the cb at top surface}
  fermibuffer :=  bandgap[3]-1.0e3; {mev} {fermi level from the vb at the buffer}
  vgs := -0.0e3;{ -4.0e3;}{gate voltage}
  mw := 0.2;              {electron effective mass in the 2d channel in m_0}
  mb := 0.2*(1.0-alz[1]) + 0.28*alz[1];  {barrier elec. effective mass in m_0}
  fact1:=2.62468e-4*dz*dz*mw;
  fact2:=2.62468e-4*dz*dz*mb;
  wkb1 := 7.0/sqrt(fact1);
  wkb2 := 7.0/sqrt(fact2);
  kt   := t_k*13.80648/1.60217657*1.0e-2; { temperature in mev  }
  for n := 1 to layer do
    vh[n] := bandoffset*(bandgap[n]-bandgap[3]); {cb barrier}
  for z := z0 to z3 do begin
    rhoa[z] := 0.0; {initialization of ionized acceptors density}
    rhod[z] := 0.0; {initialization of ionized donors density}
  end;
  if donorden > 1.0 then
    for z:= z0+1 to z2 do
      rhod[z] := donorden*dz*1.0e-12; {donor doping density}
  if acceptorden > 1.0 then
    for z := (z2+1) to za do
      rhoa[z] := acceptorden*dz*1.0e-12; {acceptor doping density}
  sf := 0.5; {initial guess of mobile and inmobil charge}
  ne := abs(pol[3]-pol[1])*sf*1.0e3/chrg;
end;

procedure cal_subbands(okay:boolean);
label 99;
const
   itmax = 100;
   eps = 1.0e-7;
   tol = 1.0e-7;
var
   a, b, c, d, e, min1, min2, min: real;
   fa, fb, fc, p, q, r, s, tol1, xm, delta: real;
   nodes, z, iter: integer;
   nsub : integer;
   sign : integer;
   del, del1,sps, del2 : real;
begin
  for Nsub :=0 to NMax do
  begin
    del :=  energy[nsub]-energy[nsub-1];
    if del < 5.0 then del := 5.0;
    if del > 20.0 then del := 20.0;
    if okay then a := energy[nsub]-del/2.0
    else begin
    if nsub = 0 then a:= 30.0 else a:= energy[nsub-1]+ del/4.0;
    end;
    del1 := del;
    sign := 0;
    repeat
    fa := fx2(a);
    check_nodes(nodes);
    if nodes < Nsub then begin
      if sign < 0 then del1 := del1/2;
      a := a + del1;
      sign := 1;
     end
    else if nodes > Nsub  then begin
      if sign > 0 then del1 := del1/2;
      a := a - del1;
      sign := -1;
    end;
   until nodes = Nsub;
   b := a+del;
   sign := 0;
   repeat
    fb := fx2(b);
    check_nodes(nodes);
    if nodes > (Nsub+1) then begin
      if sign > 0 then del1 := del1/2;
      b := b - del1;
      sign := -1;
    end
    else if nodes < (Nsub+1) then begin
      if nodes = Nsub then begin
        a := b;
        fa := fb;
      end;
      if sign < 0 then del1 := del1/2;
      b := b + del1;
      sign := 1;
    end;
   until nodes = (Nsub+1);
   if fa*fb > 0.0 then goto 99;
   fc := fb;
   for iter := 1 to itmax do begin
      if fb*fc > 0.0 then begin
         c := a;
         fc := fa;
         d := b-a;
         e := d
      end;
      if abs(fc) < abs(fb) then begin
         a := b;
         b := c;
         c := a;
         fa := fb;
         fb := fc;
         fc := fa
      end;
      tol1 := 2.0*eps*abs(b)+0.5*tol;
      xm := 0.5*(c-b);
      if (abs(xm) <= tol1) or (fb = 0.0) then begin
         energy[nsub] := b;
         zfirst[nsub] :=zmin;
         zlast[nsub] := zmax;
         sps := 0.0;
         for z := zmin to zmax do sps := sps + sqr(psi[z]);
         for z := z0 to z3 do psisq[nsub,z] := 0.0;
         for z := zmin to zmax do
         begin
          psisq[nsub,z] := sqr(psi[z])/sps;
          psi0[nsub,z] := psi[z];
          end;
         goto 99
      end;
      if (abs(e) >= tol1) and (abs(fa) > abs(fb)) then begin
         s := fb/fa;
         if a = c then begin
            p := 2.0*xm*s;
            q := 1.0-s
         end
         else begin
            q := fa/fc;
            r := fb/fc;
            p := s*(2.0*xm*q*(q-r)-(b-a)*(r-1.0));
            q := (q-1.0)*(r-1.0)*(s-1.0)
         end;
         if p > 0.0 then q := -q;
         p := abs(p);
         min1 := 3.0*xm*q-abs(tol1*q);
         min2 := abs(e*q);
         if min1 < min2 then min := min1 else min := min2;
         if 2.0*p < min then begin
            e := d;
            d := p/q
         end
         else begin
            d := xm;
            e := d
         end
      end
      else begin
         d := xm;
         e := d
      end;
      a := b;
      fa := fb;
      if abs(d) > tol1 then b := b+d
      else begin
         if xm >= 0 then b := b+abs(tol1)
         else b := b-abs(tol1);
      end;
      fb := fx2(b);
   end;
   99:
  end;
end;

procedure calfp(first:boolean; sf,ne:real; var frp, ffp, efermi: real);
var
    defield: larray;
    vref, schrg, df, dvsq, vsub : real;
    z, i, iter : integer;
    okay : boolean;
 begin
  schrg := -sf*pol[1]+ ne*chrg/1.0e3;{surface induced charge.}
  for i := 1 to 3 do defield[i] :=1.0e5*(pol[i]+schrg)/epsi[i];  {mev/a}
  for z := z0 to z1 do    v0[z] := defield[1]*z*dz;
  if z2>z1 then
    for z := z1+1 to z2 do v0[z] := v0[z1] + defield[2]*(z-z1)*dz;
  for z := z2+1 to z3 do v0[z] := v0[z2] + defield[3]*(z-z2)*dz;
  for z := z0 to z1 do    v0[z] := v0[z] + vh[1];
  if z2 > z1 then
    for z := z1+1 to z2 do v0[z] := v0[z] + vh[2];
  vref := v0[z2+1];
  for z := z0 to z3 do    v0[z] := v0[z] - vref;
  if first then
  begin
    df :=  -1.0e2*ne/epsi[3];
    for z := z0 to z2 do v[z] := v0[z];
    for z:= z2+1 to z3 do v[z] := v0[z] + df*(z-z2)*dz;
    if v[z3] < 0.0 then
    begin
      writeln('V[z3] must be positive.');
      readln;
      for z:= z2+1 to z3 do v[z] := (z-z2)*dz;
    end;
  end;
  okay := false;
  iter := 0;
  repeat
   inc(iter);
   cal_subbands (okay);
   okay := true;
   fermi_energy(ne,efermi);
   calpotential(efermi, okay, dvsq);
  until  dvsq < 1.0e-6;
  vsub := v[z3] + (v[z3]-v[z3-1])/dz*thickbuff;
  frp := vsub - bandgap[3] +fermibuffer - efermi;
  ffp := v[z0] -fermisurf - efermi +vgs;
end;

procedure select_sf_ne (var sf, ne : real);
var
    vb,vb1,vb2, schrg, vbtarget, a, b : real;
begin
    sf := 0.65;
    ne := 7.0;
    vbtarget:= 1.0e3;
    schrg := -sf*pol[1]+ ne*chrg/1.0e3;
    vb :=(pol[1]+schrg)/epsi[1]*thick[1] + (pol[2]+schrg)/epsi[2]*thick[2]+
       (pol[3]+schrg - ne*chrg/1.0e3)/epsi[3]*channelthick;
    vb1 := vb*1.0e5 - vh[1]+fermisurf - bandgap[3]-fermibuffer;
    sf := sf+0.1;
    schrg := -sf*pol[1]+ ne*chrg/1.0e3;
    vb :=(pol[1]+schrg)/epsi[1]*thick[1] +(pol[2]+schrg)/epsi[2]*thick[2]+
       (pol[3]+schrg - ne*chrg/1.0e3)/epsi[3]*channelthick;
    vb2 := vb*1.0e5 - vh[1] +fermisurf - bandgap[3]-fermibuffer;
    a := 10.0*(vb2-vb1);
    b := vb2-a*sf;
    sf :=(vbtarget - b)/a;
    ne := abs(pol[3]-pol[1])*sf*1.0e3/chrg;
end;

procedure selfcon_cal(var  sf,ne,ef:real);
var
  schrg, idchrg,iachrg,freechrg,rschrg, dx, dy: real;
  sf1, ne1, sf2, ne2,frp0, ffp0, frp1,ffp1, frp2, ffp2, frp3, ffp3:real;
  i, z: integer;
  done, first : boolean;
begin
  first := true;         {we calculate potential roughly  in the beginning.}
  select_sf_ne (sf, ne);
  calfp(first, sf,ne,frp0,ffp0, ef);
  first := false;
  dx := 1.0e-3*sf;
  dy := 0.001*ne;
  done := false;
  repeat
    sf1:= sf + dx;
    calfp(first,sf1,ne,frp1,ffp1, ef);
    sf2 := sf - (sf-sf1)*frp0/(frp0-frp1);
    calfp(first,sf2,ne,frp2,ffp2, ef);
    writeln('  sf:',sf:8:6, sf1:9:6, sf2:9:6,' r. f. pin: ',
      frp0:12,' ', frp1:12,' ',frp2:12);
    ne1 := ne - dy;
    if ne1 < minnelec then ne1 :=minnelec;
    calfp(first, sf2,ne1,frp3,ffp3, ef);
    ne2 := ne - (ne - ne1)*ffp2/(ffp2-ffp3);
    if ne2 < minnelec then
    begin
      ne2 :=minnelec;
      done := true;
    end;
    calfp(first, sf2,ne2,frp0,ffp0, ef);
    writeln('  ne:',ne:8:5, ne1:9:5,ne2:9:5,' f. f. pin: ',
    ffp2:12,' ',ffp3:12,' ',ffp0:12);
    dx := -dx/10.0;
    dy := -dy/10.0;
    sf := sf2;
    ne := ne2;
    if (abs(frp0)<1.0e-4) and (abs(ffp0)<1.0e-4) then done:= true;
    writeln;
  until done;
end;
Procedure Inigraph;
var
  gd, gm, error, dummy : smallint;
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
end;

procedure cplot(x:integer; yy:real; col:word);
var y : integer;
begin
     y:= getmaxy-10 - round (2.0*yy);
     if (y > 0) and (y <1000) then begin
         x := x div 2;
         PutPixel(x+250,y,col);
     end;
end;

procedure plotPotential;
var
   z, y1, y2, nsub, option : integer;
begin
  for z := z0 to z3 do cplot(z,V[z], white);
  if donorden > 1e-10 then
    for z := z0+1 to z2 do cplot(z,V[z]-bedon, yellow);
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
  option := 1;
  for nsub :=0 to nMax do begin
      zmin := zfirst[nsub];
      zmax := zlast[nsub];
      for z:=zmin to zmax do begin
        cplot(z,Energy[nsub], yellow);
        if option = 1 then
          cplot(z, 4.0e4*PsiSq[nsub,z]/(nsub+1) + Energy[nsub], green)
        else cplot(z, 0.5e2*Psi0[nsub,z]/(nsub+1) + Energy[nsub], green);
      end;
  end;
  z:=1;
  repeat
    cplot(z,e_fermi, red);
    z := z + 4
  until z > z3-5;
  readln;
end;

procedure SaveResults (sf,ne, ef:real);
var z, i : integer;
  schrg, idchrg,iachrg,freechrg,rschrg, xexp: real;
begin
  schrg := -sf*pol[1]+ ne*chrg/1.0e3;{front surface induced charge.}
  iachrg := ionaden*chrg/1.0e3;
  idchrg := -iondden*chrg/1.0e3;
  freechrg := -ne*chrg/1.0e3;
  rschrg := -schrg-iachrg-idchrg-freechrg;
  xexp := 0.0;
  for z:=z0 to z3 do begin
     phi[z]:=0;
     for i:=0 to nMax do phi[z]:=phi[z] + PsiSq[i,z]*Sub_density[i];
     xexp := xexp + z*phi[z];
  end;
  if ne > 1e-20 then xexp := dz*xexp/ne;
  writeln('    ne       ef  energy[0] sub_density energy[1]  sub_density   xexp');
  writeln(ne:7:4, ef:10:2, energy[0]:10:2, sub_density[0]:10:4,
   energy[1]:10:2, sub_density[1]:10:4,xexp:10:2);
  assign (OutFile, 'gan00.txt');
  Rewrite (OutFile);
  writeln(Outfile, 'barrier1 thickness (A):  ', thick[1]:7:2);
  writeln(Outfile, 'barrier2 thickness (A):  ', thick[2]:7:2);
  writeln(Outfile, 'elec. channel thickness (A):', channelthick:10:2);
  writeln(Outfile, 'donor doping density (/cm^3):', donorden:13);
  writeln(Outfile, 'acceptor doping density (/cm^3):', acceptorden:13);
  writeln(Outfile, 'barrior1 indi.concentration:', inz[1]:7:4);
  writeln(Outfile, 'barrior2 indi.concentration:', inz[2]:7:4);
  writeln(Outfile, 'elec channel indi.concentration:', inz[3]:7:4);
  writeln(Outfile, 'substrate indi.concentration:', inxsub:7:4);
  writeln(Outfile, 'barrior1 al.concentration:', alz[1]:7:4);
  writeln(Outfile, 'barrior2 al.concentration:', alz[2]:7:4);
  writeln(Outfile, 'elec. channel al.concentration:', alz[3]:7:4);
  writeln(Outfile, 'substrate al.concentration:', alxsub:7:4);
  writeln(Outfile, 'doner ion energy(meV)', bedon:7:2);
  writeln(Outfile, 'acceptor ion energy(meV)', beac:7:2);
  writeln(Outfile, 'temperature : ', t_k:7:1);
  writeln(Outfile, 'pixel size(A): ', dz :7:1);
  writeln(Outfile, 'temperature : ', t_k:7:1);
  writeln(OutFile, 'Efermi(meV) : ', ef:9:3);
  writeln(OutFile, 'x_expect(a) : ', xexp:9:3);
  writeln(OutFile, 'n_elec(e12cm-2)   : ', ne:9:5);
  writeln(OutFile,' z*dz  V[z](meV) psi^2[0] pai^2[1]...psi^2[nmax)');
  for z:=z0 to z3 do begin
     write(OutFile, z*dz:10:2,' ', V[z]:10:3);
     for i:=0 to nMax-1 do write(OutFile,' ', 1e4*PsiSq[i,z]:9:3);
     writeln(OutFile,' ',1e4*PsiSq[nMax,z]:9:3);
  end;
  writeln (OutFile, 'nsub  Energy(meV) Sub_density(10^12cm^-2)');
  for i := 0 to nMax do
    writeln (OutFile, i:3,' ',Energy[i]:9:3,' ',Sub_density[i]:13);
  close (OutFile);
  readln;
end;

{ main routine }
begin
  set_design (sf,ne,e_fermi);
  selfcon_cal (sf,ne,e_fermi);
  Inigraph;
  plotpotential;
  readln;
  closegraph;
  saveresults(sf,ne,e_fermi);
end.







