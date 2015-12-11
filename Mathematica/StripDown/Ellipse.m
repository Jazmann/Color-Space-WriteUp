(* Mathematica Package *)
(* Created by Mathematica Plugin for IntelliJ IDEA *)

(* :Title: Ellipse *)
(* :Context: Ellipse` *)
(* :Author: jaspershemilt *)
(* :Date: 2015-11-23 *)

(* :Package Version: 0.1 *)
(* :Mathematica Version: *)
(* :Copyright: (c) 2015 jaspershemilt *)
(* :Keywords: *)
(* :Discussion: *)

BeginPackage["Ellipse`"]
(* Exported symbols added here with SymbolName::usage *)


Init: Eliptical fit to the tip

In[681]:= Clear[IsEllipse]
IsEllipse[Axx_,Axy_,Ayy_,Ax_,Ay_,A0_]:=Module[{aa,bb,cc},
  aa = Axy^2-4 Axx Ayy;
  bb=Ax Axy Ay-Axx Ay^2-Ax^2 Ayy;
  cc=Axy^2/(4 Axx);
  (Axx < 0 &&  Ayy < cc && A0 > bb/aa)||( Axx > 0 &&  Ayy > cc && A0 < bb/aa)
]

In[683]:= EllipsePropertiesFromCoeffs[Axx_,Axy_,Ayy_,Ax_,Ay_,A0_]:=Module[{x0,y0,a,b,\[Theta],u1,u2,l1,l2,l3,p1,p2},

  u1= (A0 Axy^2-Ax Axy Ay+Axx Ay^2+Ax^2 Ayy);
  u2=A0 Axx Ayy;
  l1=Sqrt[Axy^2+(Axx-Ayy)^2];
  l2=Axx+Ayy;
  l3=(Axy^2-4 Axx Ayy);
  p1=(-Axy Ay+2 Ax Ayy);
  p2= (-Ax Axy+2 Axx Ay);
  {x0,y0}={p1/l3,p2/l3};
  {a,b}={Sqrt[2] Sqrt[(u1-4u2)/((l1-l2) l3)],Sqrt[2] Sqrt[(u1-4u2)/(-l3 (l1+l2) )]};
  \[Theta]=If[Axy==0,If[Axx<Ayy,0,Pi/2],If[Axx<Ayy,1/2 ArcCot[(Axx-Ayy)/Axy],Pi/2+1/2 ArcCot[(Axx-Ayy)/Axy]]];
  {{x0,y0},{a,b},\[Theta]}
]

In[684]:= Clear[EllipseCoeffsFromProperties]
EllipseCoeffsFromProperties[{{x0_,y0_},{a_,b_},\[Theta]_}]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0},
  Axx=b^2 Cos[\[Theta]]^2+a^2 Sin[\[Theta]]^2;
  Axy=-2 a^2 Cos[\[Theta]] Sin[\[Theta]]+2 b^2 Cos[\[Theta]] Sin[\[Theta]];
  Ayy=a^2 Cos[\[Theta]]^2+b^2 Sin[\[Theta]]^2;
  Ax=-2 b^2 x0 Cos[\[Theta]]^2+2 a^2 y0 Cos[\[Theta]] Sin[\[Theta]]-2 b^2 y0 Cos[\[Theta]] Sin[\[Theta]]-2 a^2 x0 Sin[\[Theta]]^2;
  Ay=-2 a^2 y0 Cos[\[Theta]]^2+2 a^2 x0 Cos[\[Theta]] Sin[\[Theta]]-2 b^2 x0 Cos[\[Theta]] Sin[\[Theta]]-2 b^2 y0 Sin[\[Theta]]^2;
  A0=-a^2 b^2+b^2 x0^2 Cos[\[Theta]]^2+a^2 y0^2 Cos[\[Theta]]^2-2 a^2 x0 y0 Cos[\[Theta]] Sin[\[Theta]]+2 b^2 x0 y0 Cos[\[Theta]] Sin[\[Theta]]+a^2 x0^2 Sin[\[Theta]]^2+b^2 y0^2 Sin[\[Theta]]^2;
  {Axx,Axy,Ayy,Ax,Ay,A0}
]

In[686]:= EllipseXFunFromProperties[{{x0_,y0_},{a_,b_},\[Theta]_}]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0},
  {Axx,Axy,Ayy,Ax,Ay,A0}=EllipseCoeffsFromProperties[{{x0,y0},{a,b},\[Theta]}];
  Function[{x},Evaluate[{(-Ay-Axy x+Sqrt[(Ay+Axy x)^2-4 Ayy (A0+Ax x+Axx x^2)])/(2 Ayy),(-Ay-Axy x-Sqrt[(Ay+Axy x)^2-4 Ayy (A0+Ax x+Axx x^2)])/(2 Ayy)}]]
]

In[687]:= EllipseYFunFromProperties[{{x0_,y0_},{a_,b_},\[Theta]_}]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0},
  {Axx,Axy,Ayy,Ax,Ay,A0}=EllipseCoeffsFromProperties[{{x0,y0},{a,b},\[Theta]}];
  Function[{y},Evaluate[{(-Ax-Axy y-Sqrt[(Ax+Axy y)^2-4 Axx (A0+Ay y+Ayy y^2)])/(2 Axx),(-Ax-Axy y+Sqrt[(Ax+Axy y)^2-4 Axx (A0+Ay y+Ayy y^2)])/(2 Axx)}]]
]

In[688]:= getModelAxis[model_]:=Module[{tt1x,tt2x,tb1x,tb2x,tt1y,tt2y,tb1y,tb2y},
  {{{tt1x,tt1y},{tt2x,tt2y}},{{tb1x,tb1y},{tb2x,tb2y}}}=model[[1]];
  ArcTan[1/2 (-tb1x-tt1x)+(tb2x+tt2x)/2,1/2 (-tb1y-tt1y)+(tb2y+tt2y)/2]
]

In[689]:= Clear[modelToPoints]
modelToPoints[model_,xPtsIn_]:=Module[{trap,elpse,elpseXLims,elpseFun,xPts,fun,pntFun},
(*Assume model is oriented with axis -Pi/4 < axis <Pi/4 *)
  trap=model[[1]];
  elpse=model[[2]];
  elpseXLims=EllipseYFunFromProperties[elpse][elpse[[1,2]]];
  elpseFun=EllipseXFunFromProperties[elpse];
  xPts=xPtsIn-Max[xPtsIn]+elpseXLims[[2]];
  fun={
    Function[{x},Evaluate[((trap[[1]][[2,2]]-trap[[1]][[1,2]])/(trap[[1]][[2,1]]-trap[[1]][[1,1]])) (x-trap[[1]][[1,1]]) + trap[[1]][[1,2]]]],
    Function[{x},Evaluate[((trap[[2]][[2,2]]-trap[[2]][[1,2]])/(trap[[2]][[2,1]]-trap[[2]][[1,1]])) (x-trap[[2]][[1,1]]) + trap[[2]][[1,2]]]]};
  pntFun={
    Function[{x},Evaluate[Piecewise[{{Sequence[],x<trap[[1,1,1]]},{{x,fun[[1]][x]},trap[[1,1,1]]<=x<=trap[[1,2,1]]},{{x,elpseFun[x][[1]]},trap[[1,2,1]]<x<=elpseXLims[[2]]},{Sequence[],elpseXLims[[2]]<x}}]]],
    Function[{x},Evaluate[Piecewise[{{Sequence[],x<trap[[2,1,1]]},{{x,fun[[2]][x]},trap[[2,1,1]]<=x<=trap[[2,2,1]]},{{x,elpseFun[x][[2]]},trap[[2,2,1]]<x<=elpseXLims[[2]]},{Sequence[],elpseXLims[[2]]<x}}]]]};
  {Map[pntFun[[1]],xPts ],Map[pntFun[[2]],xPts ]}
]

In[709]:= Clear[EllipseFitCoeffs]
EllipseFitCoeffs[points_,"AMS"]:=Module[{c,DMat,DM,P,Q,eVal,eVec,pos,A,A4,A5,A6,Axx,Axy,Ayy,Ax,Ay,A0,x0,y0,a,b,\[Theta]},
  c=Mean[points];
  DMat = (Function[{x,y},{(x-c[[1]])^2,(x-c[[1]]) (y-c[[2]]), (y-c[[2]])^2, (x-c[[1]]), (y-c[[2]]), 1}])@@@points;
  DM=(Transpose[DMat].DMat)/Length[points];
  P={{DM[[1,1]]-DM[[1,6]]^2,DM[[1,2]]-DM[[1,6]]*DM[[2,6]],DM[[1,3]]-DM[[1,6]]*DM[[3,6]],DM[[1,4]],DM[[1,5]]},{
    DM[[1,2]]-DM[[1,6]]*DM[[2,6]],DM[[2,2]]-DM[[2,6]]^2,DM[[2,3]]-DM[[2,6]]*DM[[3,6]],DM[[2,4]],DM[[2,5]]},{
    DM[[1,3]]-DM[[1,6]]*DM[[3,6]],DM[[2,3]]-DM[[2,6]]*DM[[3,6]],DM[[3,3]]-DM[[3,6]]^2,DM[[3,4]],DM[[3,5]]},{
    DM[[1,4]],DM[[2,4]],DM[[3,4]],DM[[4,4]],DM[[4,5]]},{
    DM[[1,5]],DM[[2,5]],DM[[3,5]],DM[[4,5]],DM[[5,5]]}};
  Q={{4*DM[[1,6]],2*DM[[2,6]],0,0,0},{
    2*DM[[2,6]],DM[[1,6]]+DM[[3,6]],2*DM[[2,6]],0,0},{
    0,2*DM[[2,6]],4*DM[[3,6]],0,0},{
    0,0,0,1,0},{
    0,0,0,0,1}};
  (* {eVal,eVec}=MatlabEigensystem[{P,Q}]; *)
  {eVal,eVec}=Eigensystem[{P,Q}];
  pos=Ordering[eVal,All,Less][[1]];

  A = {Sequence@@eVec[[pos]],-eVec[[pos,1;;3]].DM[[1;;3,6]]};
  A4 = A[[4]]-2 A[[1]] c[[1]]-A[[2]] c[[2]];
  A5 = A[[5]]-2 A[[3]] c[[2]]-A[[2]] c[[1]];
  A6 = A[[6]]+A[[1]] c[[1]]^2 + A[[3]] c[[2]]^2 + A[[2]] c[[1]] c[[2]]-A[[4]] c[[1]]-A[[5]] c[[2]];

  {A[[1]],A[[2]],A[[3]],A4,A5,A6}/Norm[{A[[1]],A[[2]],A[[3]],A4,A5,A6}]
]

In[711]:= EllipseFitCoeffs[points_,"Direct"]:=Module[{c,D1,D2,S1,S2,S3,eVal,eVec,pos,T,M,cond,A,A1,A4,A5,A6,Axx,Axy,Ayy,Ax,Ay,A0,x0,y0,a,b,\[Theta]},
  c=Mean[points];
  D1 = (Function[{x,y},{(x-c[[1]])^2,(x-c[[1]]) (y-c[[2]]), (y-c[[2]])^2}])@@@points;
  D2 = (Function[{x,y},{(x-c[[1]]), (y-c[[2]]), 1}])@@@points;
  S1 = Transpose[D1] . D1;
  S2 = Transpose[D1] . D2;
  S3 = Transpose[D2] . D2;
  T = - Inverse[S3] . Transpose[S2];
  M = N[Reverse[{1/2,-1,1/2} * (S1 + S2 . T)]];
  {eVal,eVec}=Eigensystem[M];
  cond = 4 eVec[[All,1]] * eVec[[All,3]] - eVec[[All,2]] * eVec[[All,2]];
  pos = Position[cond,n_ /; n>0][[1,1]];
  A1 = eVec[[pos]];
  A = {Sequence@@A1,Sequence@@(T . A1)};
  A4 = A[[4]]-2 A[[1]] c[[1]]-A[[2]] c[[2]];
  A5 = A[[5]]-2 A[[3]] c[[2]]-A[[2]] c[[1]];
  A6 = A[[6]]+A[[1]] c[[1]]^2 + A[[3]] c[[2]]^2 + A[[2]] c[[1]] c[[2]]-A[[4]] c[[1]]-A[[5]] c[[2]];
  { A[[1]], A[[2]],A[[3]], A4, A5, A6}/Norm[{A[[1]],A[[2]],A[[3]],A4,A5,A6}]
]

In[712]:= Clear[EllipseFit]
EllipseFit[points_,"AMS"]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0,x0,y0,a,b,\[Theta]},
  {Axx,Axy,Ayy,Ax,Ay,A0}=EllipseFitCoeffs[points,"AMS"];
  If[IsEllipse[Axx,Axy,Ayy,Ax,Ay,A0],
    {{x0,y0},{a,b},\[Theta]}=EllipsePropertiesFromCoeffs[Axx,Axy,Ayy,Ax,Ay,A0];
    If[a>=b,
      {{x0,y0},{a,b},\[Theta],Function[{x,y},Evaluate[{Axx,Axy,Ayy,Ax,Ay,A0}.{x^2, x y , y^2, x, y,1}]]},
      If[\[Theta]<0,
        {{x0,y0},{b,a},\[Theta]+N[Pi/2],Function[{x,y},Evaluate[{Axx,Axy,Ayy,Ax,Ay,A0}.{x^2, x y , y^2, x, y,1}]]},
        {{x0,y0},{b,a},\[Theta]-N[Pi/2],Function[{x,y},Evaluate[{Axx,Axy,Ayy,Ax,Ay,A0}.{x^2, x y , y^2, x, y,1}]]}
      ]],
    {{},{},Null,Function[{x,y},Evaluate[{Axx,Axy,Ayy,Ax,Ay,A0}.{x^2, x y , y^2, x, y, 1}]]}
  ]
]

In[714]:= EllipseFit[points_,"Direct"]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0,x0,y0,a,b,\[Theta]},
  {Axx,Axy,Ayy,Ax,Ay,A0}=EllipseFitCoeffs[points,"Direct"];
  {{x0,y0},{a,b},\[Theta]}=EllipsePropertiesFromCoeffs[Axx,Axy,Ayy,Ax,Ay,A0];
  If[a>=b,
    {{x0,y0},{a,b},\[Theta],Function[{x,y},Evaluate[{Axx,Axy,Ayy,Ax,Ay,A0}.{x^2,
      x y , y^2, x, y,1}]]},
    If[\[Theta]<0,
      {{x0,y0},{b,a},\[Theta]+N[Pi/2],Function[{x,y},Evaluate[{Axx,Axy,Ayy,Ax,Ay,A0}.{x^2, x y , y^2, x, y,1}]]},
      {{x0,y0},{b,a},\[Theta]-N[Pi/2],Function[{x,y},Evaluate[{Axx,Axy,Ayy,Ax,Ay,A0}.{x^2, x y , y^2, x, y,1}]]}
    ]]
]

In[715]:= Clear[ellipseThetaSpacings]
ellipseThetaSpacings[{x0_,y0_},{a_,b_},\[Theta]_,n_]:=Module[{perim,\[Phi],\[Delta]\[Phi],pnt,t},
  perim=N[ArcLength[{a Cos[t],b Sin[t]},{t,0,2Pi}]];
  \[Delta]\[Phi] = Function[{\[Phi]},Evaluate[(perim/n)/Sqrt[(a^2 Cos[\[Phi]]^2 + b^2 Sin[\[Phi]]^2)]]];
  \[Phi]=0;
  pnt=Table[
    \[Phi]=\[Phi]+(\[Delta]\[Phi][\[Phi]]+\[Delta]\[Phi][\[Phi]+\[Delta]\[Phi][\[Phi]]])/2,
    {i,1,n}]+\[Theta];
  Sort[Map[Mod[#,2Pi]&,pnt]]
]

In[2039]:= Block[{a = 20, b = 5, n = 40, \[Theta] = 0, x0 = 0, y0 = 0},
  ellipsePnt = EllipseFun[{x0, y0}, {a, b}, \[Theta]];
  Show[{Graphics[{FaceForm[None], EdgeForm[Black],
    Rotate[Disk[{x0, y0}, {a, b}], \[Theta]]}],
    Graphics[Map[Line[{{x0, y0}, ellipsePnt[#]}] &,
      ellipseThetaSpacings[{x0, y0}, {a, b}, \[Theta], n]]]}]
]

Out[2039]= \!\(\*
GraphicsBox[{
  {EdgeForm[GrayLevel[0]], FaceForm[None],
    GeometricTransformationBox[
      DiskBox[{0, 0}, {20., 5.}], {{{1, 0}, {0, 1}}, Center}]}, {
    LineBox[{{0, 0}, {18.361722903465925`, 1.9819045766688512`}}],
    LineBox[{{0, 0}, {15.024330440410802`, 3.300279295163379}}],
    LineBox[{{0, 0}, {11.855563791901146`, 4.026828832780226}}],
    LineBox[{{0, 0}, {9.3288012344013, 4.422764036274663}}],
    LineBox[{{0, 0}, {7.348908215007458, 4.650225451842334}}],
    LineBox[{{0, 0}, {5.7452289591863135`, 4.789261061260697}}],
    LineBox[{{0, 0}, {4.373475648861727, 4.878990102654528}}],
    LineBox[{{0, 0}, {3.10761631716393, 4.939273231112147}}],
    LineBox[{{0, 0}, {1.7860083380503473`, 4.980023683530623}}],
    LineBox[{{0, 0}, {0.05020415519602699, 4.99998424711769}}],
    LineBox[{{0, 0}, {-1.6471999775289483`, 4.983013221397951}}],
    LineBox[{{0, 0}, {-3.0009014548736346`, 4.94339578666665}}],
    LineBox[{{0, 0}, {-4.267619079450921, 4.884845362142404}}],
    LineBox[{{0, 0}, {-5.627530112516211, 4.7979872396709435`}}],
    LineBox[{{0, 0}, {-7.208412058171603, 4.663949477103648}}],
    LineBox[{{0, 0}, {-9.152600055387065, 4.445713611348919}}],
    LineBox[{{0, 0}, {-11.630020108301068`, 4.067728422293216}}],
    LineBox[{{0, 0}, {-14.7520699807945, 3.376170457057649}}],
    LineBox[{{0, 0}, {-18.124143994584546`, 2.114169524653312}}],
    LineBox[{{0, 0}, {-19.988307903843157`, 0.17094354718030308`}}],
    LineBox[{{0, 0}, {-18.588707910489045`, -1.8449244262726932`}}],
    LineBox[{{0, 0}, {-15.298315436037914`, -3.2206515724644524`}}],
    LineBox[{{0, 0}, {-12.084973304949925`, -3.983979011448917}}],
    LineBox[{{0, 0}, {-9.507793324693168, -4.398876746503873}}],
    LineBox[{{0, 0}, {-7.490742769776921, -4.636059565764301}}],
    LineBox[{{0, 0}, {-5.862794625551649, -4.780348046812351}}],
    LineBox[{{0, 0}, {-4.47722292094616, -4.873105240220001}}],
    LineBox[{{0, 0}, {-3.2077878710891583`, -4.935269097109177}}],
    LineBox[{{0, 0}, {-1.899607520930811, -4.977395725090727}}],
    LineBox[{{0, 0}, {-0.21147286297925885`, -4.999720487363664}}],
    LineBox[{{0, 0}, {1.4970441826419136`, -4.985973191835384}}],
    LineBox[{{0, 0}, {2.8763886789523005`, -4.948019731213154}}],
    LineBox[{{0, 0}, {4.141707512434408, -4.891614373608192}}],
    LineBox[{{0, 0}, {5.486774730590607, -4.808165600411921}}],
    LineBox[{{0, 0}, {7.0402247167566445`, -4.679978872398683}}],
    LineBox[{{0, 0}, {8.941681370461446, -4.472459713828782}}],
    LineBox[{{0, 0}, {11.359450657201032`, -4.115237544530502}}],
    LineBox[{{0, 0}, {14.421327248343125`, -3.4643300253818565`}}],
    LineBox[{{0, 0}, {17.820105488099095`, -2.269964762846283}}],
    LineBox[{{0, 0}, {19.9421430181362, -0.3800437346708868}}]}},
  ImageSize->{372.6015625, Automatic}]\)

In[718]:= Clear[EllipseFun];
EllipseFun[{x0_,y0_},{a_,b_},theta_]:=Module[{r},
  r=Function[{\[Theta]},Evaluate[a b /Sqrt[(b Cos[\[Theta]])^2 +(a Sin[\[Theta]])^2 ]]];
  Function[{\[Theta]},Evaluate[{x0,y0}+RotationMatrix[theta].( r[\[Theta]] {Cos[\[Theta]],Sin[\[Theta]]})]]
]

In[720]:= Clear[randomEllipse];
randomEllipse[{x0_,y0_},{a_,b_},\[Theta]_,n_,var_:1/40]:=Module[{fun,dFun},
  fun=EllipseFun[{x0,y0},{a,b},\[Theta]];
  dFun=EllipseFun[{0,0},{a,b},\[Theta]];
  Table[
    fun[t]+(dFun[t]/Norm[dFun[t]]) {RandomVariate[NormalDistribution[0,var a ]],RandomVariate[NormalDistribution[0,var b ]]}
    ,{t,ellipseThetaSpacings[{x0,y0},{a,b},\[Theta],n]}]
]

In[722]:= Clear[randomEllipse];
randomEllipse[{x0_,y0_},{a_,b_},\[Theta]_,n_,var_:1/40]:=Module[{fun,dFun},
  fun =EllipseFun[{x0,y0},{a,b},\[Theta]];
  dFun=Function[{t},Evaluate[RotationMatrix[\[Theta]].({(b Cos[t])/Sqrt[b^2 Cos[t]^2+a^2 Sin[t]^2],(a Sin[t])/Sqrt[b^2 Cos[t]^2+a^2 Sin[t]^2]})]];
  Table[
    fun[t]+(dFun[t]/Norm[dFun[t]])RandomVariate[NormalDistribution[0,var (a +b)/2]]
    ,{t,ellipseThetaSpacings[{x0,y0},{a,b},\[Theta],n]}]
]

In[724]:= EllipseNormal[{x0_,y0_},{a_,b_},\[Theta]_,\[Phi]_]:=Module[{t},
  t=\[Phi]-\[Theta];
  RotationMatrix[\[Theta]].{-((b Cos[t])/Sqrt[b^2 Cos[t]^2+a^2 Sin[t]^2]),-((a Sin[t])/Sqrt[b^2 Cos[t]^2+a^2 Sin[t]^2])}]
Begin["`Private`"]

End[] (* `Private` *)

EndPackage[]