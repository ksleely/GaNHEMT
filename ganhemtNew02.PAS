program ganhemtNew02;
uses dos, crt, graph;
const
   zm       = 1020; { total number of pixels }
   layer    = 3;
   nsubmax  = 15;   { maximum number of subbands considered in this program }
   chrg     = 1.602177; { unit charge }
   epsilon0 = 8.85418;
type
  varray     = array[0..zm] of real;
  larray     = array[1..layer] of real;
  earray     = array[0..nsubmax] of real;
  psiarray   = array[0..nsubmax,0..zm] of real;
  zarray     = array[0..nsubmax] of integer;
var
  z1,z2,z3, zmax, zmin, zpdop1, zpdop2, zndop1,zndop2 : integer;
  vsub, t_k, kt, vgs, dz:real;
  donorden,acceptorden  : real;
  nonpolchrgden, ionaden, iondden, eden, nelec : real;
  surfnonpolchrg,backschrg, iachrg, idchrg, freechrg : real;
  fermisurf,fermibuffer : real;
  alz, inz, pol, epsi, bandgap, vh, thick: larray;
  alxsub, inxsub, xexp : real;
  fact1, fact2, dvsq, mw, mb, efermi, thickbuff : real;
  surfacefac, beac, bedon: real;
  v0, v, psi, phi, rhoa, rhod : varray;
  nmax, yscale, yoffset, xoffset, xscale: integer;
  energy, sub_density : earray;
  zfirst, zlast : zarray;
  psisq :psiarray;
  fixednmax: boolean;

procedure inigraph;
var
  gd, gm, error : smallint;
  dummy : smallint;
begin
 { we have an 8 bit mode  as the default}
  gd := d8bit;
  gm := m640x480;
  getmoderange(gd,dummy,gm);
  initgraph(gd,gm,'');
  { make sure you always check graphresult! }
  error := graphresult;
  if (error <> grok) then begin
     writeln('graph driver ',gd,' graph mode ',gm,' not supported');
     halt(1)
  end;
  setviewport(0,0,getmaxx,getmaxy, clipoff);
  setbkcolor(black);
  setcolor(white);
  settextstyle(defaultfont,horizdir,1);
  clearviewport;
  cleardevice;
  yoffset := getmaxy-round(100.0*dz);
  yscale := round(2.0*dz);
  xoffset := 450;
  xscale := round(dz);
end;

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
 gay : real;
 del_1, del_2, del_3: real;
 ec, a_1, a_c, p_ce, theta_e, lambda_e, e_1, e_2, e_3  : real;
 temp: real;
 a_f, a_s : real;
 aa, bb : real;
 av1, av2, av3, av4, av5 : real;
 epsilon_xx, epsilon_zz : real;
 d_1, d_2, d_3, d_4, del_cr, del_so : real;
 c13, c33: real;
begin
 gay := 1.0 - alx - iny;
 a_f := alx*a0_aln + iny*a0_inn + gay*a0_gan;
{ a_s := a0_gan;  }
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
 del_3 := del_2; {eq.13}
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
  gay: real;
  a0_alingan : real;
  c13_alingan, c33_alingan : real;
  substrate : real;
  strain1, strain3, r_alingan : real;
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
   epsilon_gan =  8.9; {}
   epsilon_aln =  8.5;
   epsilon_inn = 15.3;
var
 ga : real;
begin
 ga := 1.0-al-iny;
 dielecconst := epsilon0*(ga*epsilon_gan
    + al*epsilon_aln + iny*epsilon_inn);
end;

procedure cplot(x:integer; yy:real; col:word);
var y : integer;
begin
     y:= yoffset - round (yy / yscale);
     if (y > 0) and (y <1000) then begin
         x := x div xscale;
         putpixel(x+xoffset,y,col);
     end;
end;

procedure cline(x1:integer; yy1:real; x2:integer; yy2:real);
var y1, y2 : integer;
begin
  if (abs(yy1/yscale) <2e3) and (abs(yy2/yscale)<2e3) then begin
     y1:= yoffset - round (yy1 / yscale);
     y2:= yoffset - round (yy2 / yscale);
       x1 := x1 div xscale;
       x2 := x2 div xscale;
       line(x1+xoffset,y1,x2+xoffset,y2);
  end;
end;

procedure hgrxy(x,y:integer);
begin
   moveto(x*8,y*16)
end;

procedure setup;
var
  bandoffset,  al, indi : real;
  pdopingst, pdopingend : real;
  ndopingwidth, pdopingwidth,
  ndopingst, ndopingend, temp, channelthick, calt : real;
  z, n : integer;
begin
{setup parameters}
  thick[1] := 200.0; {algan barrier}
  thick[2] := 10.0;  {aln blocking barrier}
  thick[3] := 1200.0;
  channelthick := 0.5e4;
  acceptorden  := 1.0e14; {4.0e17; {/cm3}}
  donorden     := 1.0e14; { 1.0e18; }{/cm3}
  acceptorden  := acceptorden/1.0e8; {/cm2/a}
  donorden     := donorden/1.0e8; { 1.0e18/1.0e8;} {/cm2/a}
  ndopingst    := 0.0;       {ndoing start position}
  ndopingwidth := thick[1];  {ndoping width}
  ndopingend   := ndopingst + ndopingwidth;
  pdopingst    := thick[1]+thick[2]; {p-doping start}
  pdopingwidth := 1.0e3; {a}  {pdoping width}
  pdopingend   := pdopingst+pdopingwidth;
  calt := pdopingend-thick[1]-thick[2];
  if thick[3] < calt then thick[3] := calt;
  thickbuff := channelthick-thick[3]; {buffer thickness - 2d channel thickness}
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
  alz[1]   := 0.3;     { al fraction }
  alz[2]   := 0.53;
  alz[3]   := 0.0;

  inz[1]   := 0.0;
  inz[2]   := 0.0;
  inz[3]   := 0.0;

  alxsub      := 0.0;
  inxsub       := 0.0;
  t_k        := 400.0;     { temperature }
  bandoffset := 0.7;
  nmax := 1;
  fixednmax := false;
  fermisurf   := 1.5e3; {mev} {fermi level from the cb at top surface}
  fermibuffer := 1.0e3; {mev} {fermi level from the vb at the buffer}
  {if a hole channel exists at the buffer interface, fermibuffer is}
  {about zero or a negative number.}
  beac       := 300.0; {acceptor level above the vb}
  bedon      := 100.0; {donor level below the cb}
  vgs := 0.0;{ -4.0e3;}{gate voltage}
  mw := 0.2;
  mb := 0.2*(1.0-alz[1]) + 0.28*alz[1];
{end of setup parameters}


{list of fixed parameters}
  fact1:=2.62468e-4 *dz*dz*mw;
  fact2:=2.62468e-4 *dz*dz*mb;
  kt   := t_k*13.80648/1.60217657*1.0e-2; { temperature in mev  }

  for n := 1 to layer do begin
    al := alz[n];
    indi := inz[n];
    bandgap[n] := 1e3*calbandgap(al,indi);
    pol[n] := polarization (al,indi);
    epsi[n] := dielecconst(al,indi);
  end;
  for n := 1 to layer do vh[n] := bandoffset*(bandgap[n]-bandgap[3]);

  for z := 1 to z3 do begin
    rhoa[z] := 0.0;
    rhod[z] := 0.0;
  end;
    zndop1 := round(ndopingst/dz);
    zndop2 := round(ndopingend/dz);
    zpdop1 := round(pdopingst/dz);
    zpdop2 := round(pdopingend/dz);
    if zpdop2 > z3 then zpdop2 := z3;
  if donorden > 1.0 then
    for z:= zndop1+1 to zndop2 do rhod[z] := donorden*dz*1.0e-12;
  {}
  if acceptorden > 1.0 then
   for z := (zpdop1+1) to zpdop2 do rhoa[z] := acceptorden*dz*1.0e-12; {}
end;

 procedure initpotential(surfacefac,nelec:real);
 var
   defield: larray;
   vref : real;
   z, i : integer;
 begin
  surfnonpolchrg := -surfacefac*pol[1]+ nelec*chrg/1.0e3;{surface induced charge.}
  for i := 1 to 3 do defield[i] :=1.0e5*(pol[i]+surfnonpolchrg)/epsi[i];  {mev/a}
  for z := 1 to z1 do    v0[z] := defield[1]*z*dz;
  if z2 > z1 then
  for z := z1+1 to z2 do v0[z] := v0[z1] + defield[2]*(z-z1)*dz;
  if z3 > z2 then
  for z := z2+1 to z3 do v0[z] := v0[z2] + defield[3]*(z-z2)*dz;
  for z := 1 to z1 do    v0[z] := v0[z] + vh[1];
  if z2 > z1 then
  for z := z1+1 to z2 do v0[z] := v0[z] + vh[2];
  vref := v0[z2+1];
  for z := 1 to z3 do    v0[z] := v0[z] - vref;
    for z :=1 to z3 do begin
      v[z] := v0[z];
      psi[z] := 0.0;
      phi[z] := 0.0;
    end;
    for i:=0 to nsubmax do begin
    { energy[i]:=20.0*(i+1);  }
     sub_density[i]:=0.0;
    end;
    efermi := 500.0;
    nmax := nmax-1;
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
           if v[z] > e then wkb:=wkb +sqrt(fact1*(v[z]-e));
     until (wkb > 7.0) or (z = z3-2 {z5-2});
     zmax:=z;
     z:=z2;
     wkb:=0.0;
     repeat
           z := z-1;
           if v[z] > e then wkb:=wkb +sqrt(fact2*(v[z]-e))
           else wkb := 0;
     until (wkb > 7.0) or (z = 2);
     zmin:=z;
end;

procedure check_nodes( var nnodes:integer);
var z, sig,old_sig, z_bot, z_top : integer;
begin
     z_bot := zmin + 5;
     z_top := zmax - 5;
     nnodes:=0;
     if psi[z_bot] > 0.0 then old_sig:= 1 else old_sig:=-1;
     for z := z_bot to z_top do begin
           if psi[z] > 0.0 then sig:=1 else sig:=-1;
           if sig <> old_sig then begin
             nnodes:= nnodes + 1;
             old_sig:=sig;
           end
     end
end;

function fx2(e: real; nsub:integer):real;
const psimin = 1e-3;
var
  ratio : real;
  z, zm, zp : integer;
begin
   findzmaxzmin(e);
   psi[zmax+1]:=psimin;
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

procedure subbands(surfacefac,nelec:real);
label 99;
const
   itmax = 100;
   eps = 1.0e-7;
   tol = 1.0e-6;
   del0 = 10.0;
var
   a, b, c, d, e: real;
   min1, min2, min: real;
   fa, fb, fc, p, q, r: real;
   s, tol1, xm: real;
   no, nodes, z, iter: integer;
   nsub : integer;
   sign, old_sign : integer;
   del, del1,sps : real;
begin
  for nsub := 0 to nmax do begin
   del := del0;
   if nsub = 0 then a := energy[0]
   else
   a := energy[nsub-1]+del/2.0;
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
   { if a >= v[1] then begin
      writeln('e : above the barrior');
      writeln (a:7:1,'  ',  v[1]:7:1);
      readln;
      halt;
      end;   }
   until (no = 1);
   del := del0;
   if nsub = 0 then b := a/2.0
   else b := (energy[nsub-1] + energy[nsub])/2.0;
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
         sps := 0.0;
         for z := zmin to zmax do sps := sps + sqr(psi[z]);
         for z := 1 to z3 do psisq[nsub,z] := 0.0;
         if sps = 0.0 then
         begin
            writeln('sps is zero.');
            readln;
         end;
         for z := zmin to zmax do  psisq[nsub,z] := sqr(psi[z])/sps;
         zfirst[nsub] := zmin;
         zlast[nsub] := zmax;
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
         else b := b-abs(tol1)
      end;
      fb := fx2(b, nsub)
   end;
  99:
  end;
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


procedure fermi_energy(nelec:real);   { newton interpolation }
var
  density2,density1, e1, e2, de  :real;
begin
  de :=1.0;
  e1 := efermi;
  density1:=fermi_density(e1);
  repeat
   e2 := e1 + de;
   density2:=fermi_density(e2);
   e1:=e1+de*(nelec-density1)/(density2-density1);
   density1 := fermi_density (e1);
  until abs(density1-nelec) < 1e-5;
  efermi := e1;
end;

procedure calpotential(a, surfacefac, nelec:real);
var
  z,i : integer;
  vold : ^varray;
  vref, temp, facceptor, fdonor: real;
begin
  new(vold);
  fermi_energy(nelec);
  ionaden := 0.0;
  iondden := 0.0;
  eden := 0.0;
  for z:=1 to z3 do begin
   vold^[z]:=v[z];
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
   eden := eden + phi[z];
   phi[z] := phi[z] + facceptor*rhoa[z] - fdonor*rhod[z];  {e12/cm2}
   ionaden := ionaden +  facceptor*rhoa[z]; {positive}
   iondden := iondden + fdonor*rhod[z];     {positive}
  end;
  surfnonpolchrg := -surfacefac*pol[1]+nelec*chrg/1.0e3;{surface induced charge.}
  nonpolchrgden := eden+ionaden-iondden; {e12/cm2}
  backschrg := -surfnonpolchrg + nonpolchrgden*chrg/1.0e3;;
  freechrg := -eden*chrg/1.0e3;
  iachrg:= -ionaden*chrg/1.0e3;    {negative}
  idchrg:= iondden*chrg/1.0e3;
  dvsq:=0.0;
 { a:= 0.4; }
  v[0] :=0.0;
  v[1]:=0.0;
  for z:=1 to z3-1 do
       v[z+1]:= phi[z-1]+10.0*phi[z]+phi[z+1] + 2.0*v[z] - v[z-1];
  for z := 1 to z3 do v[z] := -1.0e2*chrg*dz*v[z]/12.0/epsi[3] + v0[z];
  vref := v[z2+1];
  for z:=1 to z3 do begin
    v[z]:=v[z] - vref;
    dvsq := dvsq + sqr(v[z]-vold^[z]);
    v[z] := a*v[z] + (1.0-a)*vold^[z];
  end;
  vref := v[z2+1];
  for z:=1 to z3 do v[z]:=v[z] - vref;
  dvsq := sqrt(dvsq/z3);
  if sub_density[nmax] > 1.0e-6 then begin
     if not fixednmax then nmax := nmax+1;
     if nmax > nsubmax then nmax := nsubmax;
  end
  else begin
    if  sub_density[nmax-1] < 1.0e-6 then nmax := nmax-1;
  end;

  dispose(vold);
end;

procedure cal (x, y:real; var fermirearpin, fermispin: real; var iter:integer);
var a, sf,ne : real;

begin
  sf := x;
  ne := y;
  initpotential(sf,ne);
  iter := 0;
  a := 0.6;
  repeat
      inc(iter);
      subbands(sf,ne);
      calpotential(a, sf,ne);
      if dvsq > 1e-4 then a:= 0.5
      else if dvsq > 1e-5 then a := 0.3
      else a := 0.1;
  until (dvsq < 1.0e-6) or (iter > 60);
  vsub := v[z3] + (v[z3]-v[z3-1])/dz*thickbuff;
  fermirearpin := vsub - bandgap[3] +fermibuffer - efermi; {for intrinsic subs.}
  fermispin := v[1] -fermisurf - efermi +vgs;
end;


procedure plotpotential;
var
   z : integer;
begin
  for z := 1 to z3 do cplot(z,v[z], white);
end;

procedure plotresults;
var
   z, nsub, y1, y2, zt, i : integer;
   s1,s2,s3, s4, s5: string[9];
begin
   xexp := 0.0;
   for z:=1 to z3 do begin
     phi[z]:=0;
     for i:=0 to nmax do phi[z]:=phi[z] + psisq[i,z]*sub_density[i];
     xexp := xexp + z*phi[z];
   end;
   if nelec > 1e-20 then xexp := dz*xexp/nelec;
  hgrxy(3,3);
  outtext(' nsub en(mev) n_e(e12/cm2) zmin(a) zmax(a)');
  for nsub := 0 to nmax do begin
   str(nsub:3,s1); str(energy[nsub]:8:2,s2); str(sub_density[nsub]:8:5,s3);
   str(zfirst[nsub]*dz:8:1,s4);  str(zlast[nsub]*dz:8:1,s5);
   hgrxy(3, 4+nsub); outtext(' '+s1+' '+s2+' '+s3+' '+s4+' '+s5);
  end;

  hgrxy(3,8+nmax); str(efermi:9:2,s1); outtext('efermi (mev)        : '+s1);
  hgrxy(3,9+nmax); str(xexp:9:2,s1);   outtext('<x> (a)             :'+s1);

  hgrxy(3,10+nmax); str(surfacefac:9:7,s1); outtext('surface factor      : '+s1);
  hgrxy(3,11+nmax);str(v[1]:9:2,s1); str(v[1]-bandgap[1]:9:2,s2);
  outtext('surf. vc (mev)      : '+s1+ '   vv : '+s2);
  hgrxy(3,12+nmax);str(vsub:9:2,s1);  str(vsub-bandgap[3]:9:2,s2);
  outtext('subs. vc (mev)      : '+s1+ '   vv : '+s2);
  hgrxy(3,13+nmax);str(dz:5:2,s1); outtext('dz(ang)        : '+s1);

  surfnonpolchrg := -surfacefac*pol[1]+nelec*chrg/1.0e3;{surface induced charge.}
  nonpolchrgden := eden+ionaden-iondden;
  freechrg := -eden*chrg/1.0e3;
  iachrg:= -ionaden*chrg/1.0e3;    {negative}
  backschrg := -surfnonpolchrg + nonpolchrgden*chrg/1.0e3;;
  idchrg:= iondden*chrg/1.0e3;

  hgrxy(3,14+nmax);str(surfnonpolchrg:9:5,s1);
  outtext('surf. cd(c/m2): '+s1);

  str(freechrg:9:5,s1);
  hgrxy(3,15+nmax);str(eden:9:5,s2);
  outtext('elec den. (e12/cm2): '+s1+'  '+s2);

  hgrxy(3,16+nmax);str(iachrg:9:5,s1);  str(ionaden:9:5,s2);
  outtext('ion ac cd (c/m2)(e12/cm2): '+s1+'  '+s2);

  hgrxy(3,17+nmax);str(iondden:9:5,s2); str(idchrg:9:5,s1);
  outtext('ion donor cd. (c/m2)(e12/cm2): '+s1+'  '+s2);

  hgrxy(3,20+nmax);str(backschrg:9:5,s1);
  outtext('rear surf. cd(c/m2): '+s1);



  if donorden > 1e-10 then
   for z := zndop1+1 to zndop2 do cplot(z,v[z]-bedon, yellow);
  for z := 1 to z1 do cplot(z,v[z]-bandgap[1], white);
  if z2 > z1 then
  for z := z1+1 to z2 do cplot(z,v[z]-bandgap[2], white);
  if z3 > z2 then
  for z := z2+1 to z3 do cplot(z,v[z]-bandgap[3], white);


  if zpdop2 > zpdop1 then
  begin
  if acceptorden > 1.0e-10 then
   for z := zpdop1+1 to zpdop2 do cplot(z,v[z]-bandgap[3] + beac, blue);
  end;

  y1 := round(v[1]-bandgap[1]);
  y2 := round(v[1]);
  for z := y1 to y2 do cplot(0, 1.0*z, white);


  y1 := round(v[z1-1]);
  y2 := round(v[z1+1]);
  if y1 > y2 then
  for z := y1 downto y2 do cplot(z1, 1.0*z, white)
  else  for z := y1 to y2 do cplot(z1, 1.0*z, white);

  y1 := round(v[z2-1]);
  y2 := round(v[z2+1]);
  if y1 > y2 then
  for z := y1 downto y2 do cplot(z2, 1.0*z, white)
  else  for z := y1 to y2 do cplot(z2, 1.0*z, white);
  for nsub :=0 to nmax do begin
      zmin := zfirst[nsub];
      zmax := zlast[nsub];
      for z:=zmin to zmax do begin
        cplot(z,energy[nsub], yellow);
        cplot(z, 1e4*psisq[nsub,z] + energy[nsub], green);
      end;
   end;
  z:=1;
  zt := z3;
  repeat
         cplot(z,efermi, red);
         z := z + 4
  until z > zt;
end;

procedure newtoninterpol;

var x0, x1,x2, dx, dy, rearpin0, rearpin1, rearpin2, rearpin3,
    fermipin1, fermipin0, fermipin2, fermipin3,
    y0, y1,y2, tobezero : real;
    iter1, i : integer;
begin
  writeln ('x0      y0    rearpin0   fermipin0  dvsq tobezero iter1');

  nelec := 1.0;
  surfacefac := 0.55;
  x0 := surfacefac;
  y0 := nelec;
  dx := 0.001;
  dy := nelec/2.0;
for i := 1 to 5 do
begin
  cal(x0, y0, rearpin0, fermipin0,iter1);
{  writeln(x0:10:5, y0:10:5, rearpin0:13:5,fermipin0:13:5);  }
  if rearpin0 > 0.0 then x1 := x0 + dx else x1:= x0 - dx;
  if fermipin0 > 0.0 then y1 := y0 + dy else y1:= y0 - dy;

  cal(x1, y0, rearpin1, fermipin1,iter1);
{  writeln(x1:10:5, y0:10:5, rearpin1:13:5,fermipin1:13:5);  }

  x2 := x0 - 0.9*(x0-x1)*rearpin0/(rearpin0-rearpin1);
  cal(x2, y0, rearpin2, fermipin2,iter1);
{  writeln(x2:10:5, y0:10:5, rearpin2:13:5,fermipin2:13:5); }

  cal(x2, y1, rearpin3, fermipin3,iter1);
{  writeln(x2:10:5, y1:10:5, rearpin3:13:5,fermipin3:13:5); }

  y2 := y0 - (y0 - y1)*fermipin2/(fermipin2-fermipin3);
  cal(x2, y2, rearpin3, fermipin3,iter1);
{  writeln(x2:10:5, y2:10:5, rearpin3:13:5,fermipin3:13:5); }
   tobezero := abs(rearpin3)+abs(fermipin3);
{   writeln (x2:11:9,' ',y2:11:8,' ',rearpin2:11:4,' ',fermipin3:11:4,' ',
         dvsq*1e6:7:2,' ',tobezero:13,' ',iter1:2,' ',iter:3); }
  x0 := x2;
  y0 := y2;
  dx := dx/10.0;
  dy := dy/10.0;
 end;

  cal(x0, y0, rearpin0, fermipin0,iter1);
{  writeln(x0:10:5, y0:10:5, rearpin0:13:5,fermipin0:13:5);  }
  if rearpin0 > 0.0 then x1 := x0 + dx else x1:= x0 - dx;
  if fermipin0 > 0.0 then y1 := y0 + dy else y1:= y0 - dy;

  cal(x1, y0, rearpin1, fermipin1,iter1);
{  writeln(x1:10:5, y0:10:5, rearpin1:13:5,fermipin1:13:5); }

  x2 := x0 - 1.0*(x0-x1)*rearpin0/(rearpin0-rearpin1);
  cal(x2, y0, rearpin2, fermipin2,iter1);
{  writeln(x2:10:5, y0:10:5, rearpin2:13:5,fermipin2:13:5); }

  cal(x2, y1, rearpin3, fermipin3,iter1);
{  writeln(x2:10:5, y1:10:5, rearpin3:13:5,fermipin3:13:5); }

  y2 := y0 - (y0 - y1)*fermipin2/(fermipin2-fermipin3);
  cal(x2, y2, rearpin3, fermipin3,iter1);
 { writeln(x2:10:5, y2:10:5, rearpin3:13:5,fermipin3:13:5); }

   tobezero := abs(rearpin3)+abs(fermipin3);
   writeln (x2:11:9,' ',y2:11:8,' ',rearpin3:11:4,' ',fermipin3:11:4,' ',
         dvsq*1e6:7:2,' ',tobezero:13,' ',iter1:2);
  surfacefac := x2;
  nelec := y2;
end;



procedure saveresults;
var z, i : integer;
    fermipinsubs, fermipinsurf: real;
    outfile : text;
begin
   assign (outfile, 'gan00.txt');
   rewrite (outfile);
   write(outfile, 'z*dz(A)  v[z](meV) phi[z]/dz ');
   write(outfile,' psi_sq[0,z] psi_sq[1,z]....' );
   writeln(outfile,' psi_sq[nmax,z]');
   for z:=1 to z3 do begin
     write(outfile, z*dz:7:1,' ', v[z]:8:2,' ',1e2*phi[z]/dz:7:5);
     for i:=0 to nmax-1 do write(outfile,' ', 1e4*psisq[i,z]:7:3);
     writeln(outfile,' ',1e4*psisq[nmax,z]:7:3);
   end;
   fermipinsubs := vsub-efermi;
   fermipinsurf := v[1] - efermi;
   writeln (outfile, 'efermi(mev)      : ', efermi:7:2);
   writeln (outfile, 'v_buffer-efermi(mev): ', fermipinsubs:7:1);
   writeln (outfile, 'v_surface-efermi(mev) : ', fermipinsurf:7:1);
   writeln (outfile, 'x_expect(a)      : ', xexp:7:2);
   writeln (outfile, 'nelec(e12cm-2)   : ', nelec:7:5);
   writeln (outfile, 'surfacefac       : ', surfacefac:7:5);
   writeln (outfile, 'surf-charge(c/m2): ', surfnonpolchrg:13);
   for i := 0 to nmax do
    writeln (outfile, i:3,' ',energy[i]:7:2,' ',sub_density[i]:7:5);
   close (outfile);
end;

{ main routine }
begin
  setup;
  newtoninterpol;
  inigraph;
  plotpotential;
  plotresults;
  readln;
  closegraph;
 saveresults;
end.
