(* ::Package:: *)

Clear[ShowFun]
SetAttributes[ShowFun,HoldAllComplete];
ShowFun[f_[args__]]:=Row[{TraditionalForm[f[Sequence@@Map[ToString,{args}]]]," = ",TraditionalForm[f[args]]}]


(* ::Section:: *)
(*Rotation Matrices*)


ClearAll[RotationMatrixX,RotationMatrixY,RotationMatrixZ,R,\[Alpha]]
RotationMatrixX[\[Alpha]:Except[_String]]:={{1, 0, 0}, {0, Cos[\[Alpha]], Sin[\[Alpha]]}, {0, -Sin[\[Alpha]], Cos[\[Alpha]]}};
Format[RotationMatrixX, TraditionalForm]=TraditionalForm["\!\(\*SubscriptBox[\(R\), \(X\)]\)"];
RotationMatrixY[\[Beta]:Except[_String]]:={{Cos[\[Beta]], 0, -Sin[\[Beta]]}, {0, 1, 0}, {Sin[\[Beta]], 0, Cos[\[Beta]]}};
Format[RotationMatrixY, TraditionalForm]=TraditionalForm["\!\(\*SubscriptBox[\(R\), \(Y\)]\)"];
RotationMatrixZ[\[Gamma]:Except[_String]]:={{Cos[\[Gamma]], Sin[\[Gamma]], 0}, {-Sin[\[Gamma]], Cos[\[Gamma]], 0}, {0, 0, 1}};
Format[RotationMatrixZ, TraditionalForm]=TraditionalForm["\!\(\*SubscriptBox[\(R\), \(Z\)]\)"];
RotationMatrixXYZ[\[Alpha]:Except[_String],\[Beta]:Except[_String],\[Gamma]:Except[_String]]:=Evaluate[TrigReduce[RotationMatrixX[\[Alpha]].RotationMatrixZ[\[Gamma]].RotationMatrixY[\[Beta]]]];
Format[RotationMatrixXYZ, TraditionalForm]=TraditionalForm["\!\(\*SubscriptBox[\(R\), \(XYZ\)]\)"];


RotationMatrixLCaCb[\[Theta]:Except[_String]]:= Evaluate[TrigFactor[RotationMatrixX[\[Theta]].RotationMatrixZ[ArcTan[1/Sqrt[2]]].RotationMatrixY[-Pi/4]]];
Format[RotationMatrixLCaCb, TraditionalForm]=TraditionalForm["\!\(\*
StyleBox[\"R\",\nFontWeight->\"Bold\"]\)"];
iRotationMatrix[\[Theta]:Except[_String]]:= Evaluate[TrigFactor[RotationMatrixY[Pi/4].RotationMatrixZ[-ArcTan[1/Sqrt[2]]].RotationMatrixX[-\[Theta]]]];
Format[iRotationMatrix, TraditionalForm]=TraditionalForm["\!\(\*
StyleBox[SuperscriptBox[
StyleBox[\"R\",\nFontWeight->\"Bold\"], 
RowBox[{\"-\", \"1\"}]],\nFontWeight->\"Bold\"]\)"];


rR[\[Theta]_]:= ({
 {1, 1, 1},
 {- Sin[\[Theta]+\[Pi]/6],  Cos[\[Theta]],  Sin[\[Theta]-\[Pi]/6]},
 {- Cos[\[Theta]+\[Pi]/6], - Sin[\[Theta]],  Cos[\[Theta]-\[Pi]/6]}
})


irR[\[Theta]_]:={{1/3, (-(2/3))*Sin[Pi/6 + \[Theta]], (-(2/3))*Cos[Pi/6 + \[Theta]]}, {1/3, (2*Cos[\[Theta]])/3, -((2*Sin[\[Theta]])/3)}, {1/3, (-(2/3))*Sin[Pi/6 - \[Theta]], (2/3)*Cos[Pi/6 - \[Theta]]}}


Clear[scale];
scale["LCaCb","rR"] = {1/Sqrt[3],Sqrt[2/3],Sqrt[2/3]};
scale["nLCaCb","LCaCb"][\[Theta]_] := {1/Sqrt[3],1/2 Sqrt[3/2] Sec[\[Pi]/6 - Mod[\[Theta]-\[Pi]/6,\[Pi]/3]],1/2 Sqrt[3/2] Sec[\[Pi]/6 - Mod[\[Theta],\[Pi]/3]]}
scale["nLCaCb","rR"][\[Theta]_]:= {1/3,1/2 Sec[\[Pi]/6-Mod[-(\[Pi]/6)+\[Theta],\[Pi]/3]],1/2 Sec[\[Pi]/6-Mod[\[Theta],\[Pi]/3]]}
scale["rR","fR"][\[Theta]_]:= Piecewise[{{{1, Cos[\[Theta]], Cos[Pi/6 - \[Theta]]}, Inequality[0, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/6] || 
    Inequality[Pi, LessEqual, Mod[\[Theta], 2*Pi], Less, (7*Pi)/6]}, {{1, -Sin[Pi/6 + \[Theta]], Cos[Pi/6 - \[Theta]]}, 
   Inequality[Pi/6, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/3] || Inequality[(7*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, (4*Pi)/3]}, 
  {{1, -Sin[Pi/6 + \[Theta]], -Sin[\[Theta]]}, Inequality[Pi/3, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/2] || 
    Inequality[(4*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (3*Pi)/2]}, {{1, -Sin[Pi/6 - \[Theta]], -Sin[\[Theta]]}, 
   Inequality[Pi/2, LessEqual, Mod[\[Theta], 2*Pi], Less, (2*Pi)/3] || Inequality[(3*Pi)/2, LessEqual, Mod[\[Theta], 2*Pi], Less, 
     (5*Pi)/3]}, {{1, -Sin[Pi/6 - \[Theta]], -Cos[Pi/6 + \[Theta]]}, Inequality[(2*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (5*Pi)/6] || 
    Inequality[(5*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (11*Pi)/6]}, {{1, Cos[\[Theta]], -Cos[Pi/6 + \[Theta]]}, 
   Inequality[(5*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi] || Inequality[(11*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, 2*Pi]}}, 0]
scale["rR", "qR"][\[Theta]_, n_: 8] := Piecewise[{{{1, -(2^(2 - n)*Sin[Pi/6 + \[Theta]]), -(2^(2 - n)*Cos[Pi/6 + \[Theta]])}, Inequality[0, LessEqual, Mod[\[Theta], Pi/2], Less, Pi/6]},
   {{1, 2^(2 - n)*Cos[\[Theta]], -(2^(2 - n)*Sin[\[Theta]])}, Inequality[Pi/6, LessEqual, Mod[\[Theta], Pi/2], Less, Pi/3]},
   {{1, -(2^(2 - n)*Sin[Pi/6 - \[Theta]]), 2^(2 - n)*Cos[Pi/6 - \[Theta]]}, Inequality[Pi/3, LessEqual, Mod[\[Theta], Pi/2], Less, Pi/2]}}, Null]
scale["qR","rR"][\[Theta]_,n_:8]:=Piecewise[{{{1,-(2^(-2+n)*Csc[Pi/6+\[Theta]]),-(2^(-2+n)*Sec[Pi/6+\[Theta]])},Inequality[0,LessEqual,Mod[\[Theta],Pi/2],Less,Pi/6]},
{{1,2^(-2+n)*Sec[\[Theta]],-(2^(-2+n)*Csc[\[Theta]])},Inequality[Pi/6,LessEqual,Mod[\[Theta],Pi/2],Less,Pi/3]},
{{1,-(2^(-2+n)*Csc[Pi/6-\[Theta]]),2^(-2+n)*Sec[Pi/6-\[Theta]]},Inequality[Pi/3,LessEqual,Mod[\[Theta],Pi/2],Less,Pi/2]}},Null]
scale["qR","fR"][\[Theta]_,n_:8]:={1,2^(n-2),2^(n-2)};
scale["fR","qR"][\[Theta]_,n_:8]:={1,2^(2-n),2^(2-n)};


(* ::Text:: *)
(*rRScale["LCaCb", "rR"] = scale["LCaCb", "rR"];*)
(*nRScale[\[Theta]_] := scale["nLCaCb", "LCaCb"][\[Theta]]*)
(*nrRScale[\[Theta]_] := scale["nLCaCb", "rR"][\[Theta]]*)
(*fRScale[\[Theta]_, rRange_: 1] := scale["rR", "fR"][\[Theta], rRange]*)
(*qRScale[\[Theta]_, n_: 8] := scale["rR", "qR"][\[Theta], n]*)


Clear[fR];
fR[\[Theta]_]:=Piecewise[{{{{1, 1, 1}, {-(Sec[\[Theta]]*Sin[Pi/6 + \[Theta]]), 1, -(Sec[\[Theta]]*Sin[Pi/6 - \[Theta]])}, 
    {-(Cos[Pi/6 + \[Theta]]*Sec[Pi/6 - \[Theta]]), -(Sec[Pi/6 - \[Theta]]*Sin[\[Theta]]), 1}}, Inequality[0, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/6] || 
    Inequality[Pi, LessEqual, Mod[\[Theta], 2*Pi], Less, (7*Pi)/6]}, 
  {{{1, 1, 1}, {1, -(Cos[\[Theta]]*Csc[Pi/6 + \[Theta]]), Csc[Pi/6 + \[Theta]]*Sin[Pi/6 - \[Theta]]}, {-(Cos[Pi/6 + \[Theta]]*Sec[Pi/6 - \[Theta]]), 
     -(Sec[Pi/6 - \[Theta]]*Sin[\[Theta]]), 1}}, Inequality[Pi/6, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/3] || 
    Inequality[(7*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, (4*Pi)/3]}, 
  {{{1, 1, 1}, {1, -(Cos[\[Theta]]*Csc[Pi/6 + \[Theta]]), Csc[Pi/6 + \[Theta]]*Sin[Pi/6 - \[Theta]]}, {Cos[Pi/6 + \[Theta]]*Csc[\[Theta]], 1, 
     -(Cos[Pi/6 - \[Theta]]*Csc[\[Theta]])}}, Inequality[Pi/3, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/2] || 
    Inequality[(4*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (3*Pi)/2]}, 
  {{{1, 1, 1}, {Csc[Pi/6 - \[Theta]]*Sin[Pi/6 + \[Theta]], -(Cos[\[Theta]]*Csc[Pi/6 - \[Theta]]), 1}, {Cos[Pi/6 + \[Theta]]*Csc[\[Theta]], 1, 
     -(Cos[Pi/6 - \[Theta]]*Csc[\[Theta]])}}, Inequality[Pi/2, LessEqual, Mod[\[Theta], 2*Pi], Less, (2*Pi)/3] || 
    Inequality[(3*Pi)/2, LessEqual, Mod[\[Theta], 2*Pi], Less, (5*Pi)/3]}, 
  {{{1, 1, 1}, {Csc[Pi/6 - \[Theta]]*Sin[Pi/6 + \[Theta]], -(Cos[\[Theta]]*Csc[Pi/6 - \[Theta]]), 1}, {1, Sec[Pi/6 + \[Theta]]*Sin[\[Theta]], 
     -(Cos[Pi/6 - \[Theta]]*Sec[Pi/6 + \[Theta]])}}, Inequality[(2*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (5*Pi)/6] || 
    Inequality[(5*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (11*Pi)/6]}, 
  {{{1, 1, 1}, {-(Sec[\[Theta]]*Sin[Pi/6 + \[Theta]]), 1, -(Sec[\[Theta]]*Sin[Pi/6 - \[Theta]])}, {1, Sec[Pi/6 + \[Theta]]*Sin[\[Theta]], 
     -(Cos[Pi/6 - \[Theta]]*Sec[Pi/6 + \[Theta]])}}, Inequality[(5*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi] || 
    Inequality[(11*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, 2*Pi]}}, 0];


(* ::Text:: *)
(**)


qR[\[Theta]_,n_:8]:=Piecewise[{{{{1, 1, 1}, {-Round[2^(-2 + n)*Sec[\[Theta]]*Sin[Pi/6 + \[Theta]]], Round[2^(-2 + n)], 
     -Round[2^(-2 + n)*Sec[\[Theta]]*Sin[Pi/6 - \[Theta]]]}, {-Round[2^(-2 + n)*Cos[Pi/6 + \[Theta]]*Sec[Pi/6 - \[Theta]]], 
     -Round[2^(-2 + n)*Sec[Pi/6 - \[Theta]]*Sin[\[Theta]]], Round[2^(-2 + n)]}}, Inequality[0, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/6] || 
    Inequality[Pi, LessEqual, Mod[\[Theta], 2*Pi], Less, (7*Pi)/6]}, 
  {{{1, 1, 1}, {Round[2^(-2 + n)], -Round[2^(-2 + n)*Cos[\[Theta]]*Csc[Pi/6 + \[Theta]]], Round[2^(-2 + n)*Csc[Pi/6 + \[Theta]]*Sin[Pi/6 - \[Theta]]]}, 
    {-Round[2^(-2 + n)*Cos[Pi/6 + \[Theta]]*Sec[Pi/6 - \[Theta]]], -Round[2^(-2 + n)*Sec[Pi/6 - \[Theta]]*Sin[\[Theta]]], Round[2^(-2 + n)]}}, 
   Inequality[Pi/6, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/3] || Inequality[(7*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, (4*Pi)/3]}, 
  {{{1, 1, 1}, {Round[2^(-2 + n)], -Round[2^(-2 + n)*Cos[\[Theta]]*Csc[Pi/6 + \[Theta]]], Round[2^(-2 + n)*Csc[Pi/6 + \[Theta]]*Sin[Pi/6 - \[Theta]]]}, 
    {Round[2^(-2 + n)*Cos[Pi/6 + \[Theta]]*Csc[\[Theta]]], Round[2^(-2 + n)], -Round[2^(-2 + n)*Cos[Pi/6 - \[Theta]]*Csc[\[Theta]]]}}, 
   Inequality[Pi/3, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi/2] || Inequality[(4*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (3*Pi)/2]}, 
  {{{1, 1, 1}, {Round[2^(-2 + n)*Csc[Pi/6 - \[Theta]]*Sin[Pi/6 + \[Theta]]], -Round[2^(-2 + n)*Cos[\[Theta]]*Csc[Pi/6 - \[Theta]]], Round[2^(-2 + n)]}, 
    {Round[2^(-2 + n)*Cos[Pi/6 + \[Theta]]*Csc[\[Theta]]], Round[2^(-2 + n)], -Round[2^(-2 + n)*Cos[Pi/6 - \[Theta]]*Csc[\[Theta]]]}}, 
   Inequality[Pi/2, LessEqual, Mod[\[Theta], 2*Pi], Less, (2*Pi)/3] || Inequality[(3*Pi)/2, LessEqual, Mod[\[Theta], 2*Pi], Less, 
     (5*Pi)/3]}, {{{1, 1, 1}, {Round[2^(-2 + n)*Csc[Pi/6 - \[Theta]]*Sin[Pi/6 + \[Theta]]], -Round[2^(-2 + n)*Cos[\[Theta]]*Csc[Pi/6 - \[Theta]]], 
     Round[2^(-2 + n)]}, {Round[2^(-2 + n)], Round[2^(-2 + n)*Sec[Pi/6 + \[Theta]]*Sin[\[Theta]]], 
     -Round[2^(-2 + n)*Cos[Pi/6 - \[Theta]]*Sec[Pi/6 + \[Theta]]]}}, Inequality[(2*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (5*Pi)/6] || 
    Inequality[(5*Pi)/3, LessEqual, Mod[\[Theta], 2*Pi], Less, (11*Pi)/6]}, 
  {{{1, 1, 1}, {-Round[2^(-2 + n)*Sec[\[Theta]]*Sin[Pi/6 + \[Theta]]], Round[2^(-2 + n)], -Round[2^(-2 + n)*Sec[\[Theta]]*Sin[Pi/6 - \[Theta]]]}, 
    {Round[2^(-2 + n)], Round[2^(-2 + n)*Sec[Pi/6 + \[Theta]]*Sin[\[Theta]]], -Round[2^(-2 + n)*Cos[Pi/6 - \[Theta]]*Sec[Pi/6 + \[Theta]]]}}, 
   Inequality[(5*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, Pi] || Inequality[(11*Pi)/6, LessEqual, Mod[\[Theta], 2*Pi], Less, 2*Pi]}}, 0]


(* ::Section:: *)
(*Cube Functions*)


cubeFaces[minMax:{{_,_},{_,_},{_,_}}]:=Block[{midPts},midPts=MapThread[Plus,Transpose[minMax]]/2;{{minMax[[1,1]],minMax[[1,2]],midPts[[1]],      midPts[[1]],      midPts[[1]],midPts[[1]]},{midPts[[2]],      midPts[[2]],      minMax[[2,1]],minMax[[2,2]],midPts[[2]],midPts[[2]]},{midPts[[3]],      midPts[[3]],      midPts[[3]],      midPts[[3]],      minMax[[3,1]],minMax[[3,2]]}}]


cubeFacesInside[minMax:{{_,_},{_,_},{_,_}},delta_]:=Block[{midPts},midPts=MapThread[Plus,Transpose[minMax]]/2;{{minMax[[1,1]]+delta,minMax[[1,2]]-delta,midPts[[1]],                      midPts[[1]],                     midPts[[1]],                     midPts[[1]]},{midPts[[2]],                     midPts[[2]],                      minMax[[2,1]]+delta,minMax[[2,2]]-delta,midPts[[2]],                     midPts[[2]]},{midPts[[3]],                     midPts[[3]],                      midPts[[3]],                      midPts[[3]],                     minMax[[3,1]]+delta,minMax[[3,2]]-delta}}]


cubeCorners[minMax:{{_,_},{_,_},{_,_}}]:={
{minMax[[1,1]],minMax[[1,2]],minMax[[1,2]],minMax[[1,1]],minMax[[1,1]],minMax[[1,1]],minMax[[1,2]],minMax[[1,2]]},
{minMax[[2,1]],minMax[[2,1]],minMax[[2,2]],minMax[[2,2]],minMax[[2,2]],minMax[[2,1]],minMax[[2,1]],minMax[[2,2]]},
{minMax[[3,1]],minMax[[3,1]],minMax[[3,1]],minMax[[3,1]],minMax[[3,2]],minMax[[3,2]],minMax[[3,2]],minMax[[3,2]]}}


faces = {{1,2,3,4},{5,6,7,8},{1,2,7,6},{2,3,8,7},{3,4,5,8},{1,4,5,6}};


(* ::Subsection:: *)
(*RGB Cube*)


RGBAxisRanges = {{0,1},{0,1},{0,1}};


RGBCube["RGB"]=cubeCorners[RGBAxisRanges];
RGBCube["LCaCb"]=Function[{\[Theta]},Evaluate[TrigFactor[FullSimplify[TrigToExp[LCaCb[\[Theta]].RGBCube["RGB"]]]]]];


RGBCube3D[corners_]:=Module[{RGBCube,faces,ranges},
ranges =Transpose[{ Map[Min,corners],Map[Max,corners]}];
Graphics3D[{
Polygon[corners[[faces[[1]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[1]]]]]]],
Polygon[corners[[faces[[2]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[2]]]]]]],
Polygon[corners[[faces[[3]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[3]]]]]]],
Polygon[corners[[faces[[4]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[4]]]]]]],
Polygon[corners[[faces[[5]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[5]]]]]]],
Polygon[corners[[faces[[6]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[6]]]]]]]},
Lighting->"Neutral",
PlotRange->{{ranges[[1,1]],ranges[[1,2]]},{ranges[[2,1]],ranges[[2,2]]},{ranges[[3,1]],ranges[[3,2]]}},
Axes->True]
]


RGBCubeFinite3D[n_]:=Raster3D[Table[List[r,g,b],{b,0,1,1/n},{g,0,1,1/n},{r,0,1,1/n}],{{0,0,0},{1,1,1}},ColorFunction->RGBColor];


ball[{r_,g_,b_},radius_,n_]:=Module[{chn,color,rgbCenter},
color=RGBColor[(r)/n,(g)/n,(b)/n];
rgbCenter={r,g,b};
{color,Sphere[rgbCenter,radius]}]
balls[map_,radius_]:=Module[{chn,nR,nG,nB,color,rgbCenter},
{chn,nR,nG,nB}=Dimensions[map];
Flatten[Table[
color=RGBColor[(r)/nR,(g)/nG,(b)/nB];
rgbCenter=Part[map,All,r+1,g+1,b+1];
{color,Sphere[rgbCenter,radius]},{b,0,nB-1},{g,0,nG-1},{r,0,nR-1}]]
]


Clear[RGBCubeInYabFiniteBalls];
RGBCubeInYabFiniteBalls[\[Theta]_,cut_:3,n_:8,opacity_:{1,0.03}]:=Module[{cube,color,rgbCenter,radius,T},
T=LCaCb[\[Theta]];
cube=Flatten[Table[
color=RGBColor[(r)/n,(g)/n,(b)/n];
rgbCenter = T . List[(r)/n,(g)/n,(b)/n];
radius=1/(2n);
{Opacity[If[r+g+b < n cut, opacity[[1]], opacity[[2]] ]],color,Sphere[rgbCenter,radius]},{b,0,n-1},{g,0,n-1},{r,0,n-1}]]
]


(* ::Subsection:: *)
(*LCaCb Cube*)


LCaCbAxisRanges[\[Theta]_]:={{0,Sqrt[3]},{-Sqrt[(2/3)] Cos[\[Pi]/6-Mod[\[Theta] -Pi/6,Pi/3]] ,Sqrt[2/3] Cos[\[Pi]/6-Mod[\[Theta] -Pi/6,Pi/3]]},{-Sqrt[(2/3)] Cos[\[Pi]/6-Mod[\[Theta],Pi/3]] ,Sqrt[2/3] Cos[\[Pi]/6-Mod[\[Theta],Pi/3]]}}


LCaCbAxisLengths = Function[{\[Theta]},Evaluate[Flatten[LCaCbAxisRanges[\[Theta]][[All,2]] - LCaCbAxisRanges[\[Theta]][[All,1]]]]];


LCaCbCube["LCaCb"][\[Theta]_]:=cubeCorners[LCaCbAxisRanges[\[Theta]]];
LCaCbCube["RGB"]=Function[{\[Theta]},Evaluate[TrigFactor[FullSimplify[TrigToExp[iLCaCb[\[Theta]].LCaCbCube["LCaCb"][\[Theta]]]]]]];


(* ::Subsubsection:: *)
(*Color*)


SetUpLCaCbColor[\[Theta]_] :=Module[{theta}, LCaCbColorTheta=\[Theta];
LCaCbColorFastList=Compile[{{yIn, _Real},{aIn, _Real},{bIn, _Real}}, Module[{y,a,b,h,s,angle},
{Quiet[Mod[(ArcTan[(aIn-0.5),(bIn-0.5)]-theta-4 Pi/3),2 Pi]/(2 Pi)/.Indeterminate->0,{ArcTan::indet}],
Sqrt[2]*Sqrt[(aIn-0.5)^2+(bIn-0.5)^2],
yIn}
]]/.{theta -> \[Theta]};
LCaCbColorFast=Hue[LCaCbColorFastList[##]]&;
]


Clear[LCaCbColorFastTheta]
LCaCbColorFastTheta[yIn_,aIn_,bIn_,\[Theta]In_]:= Module[{y,a,b,h,s,angle},
y=yIn; a = aIn-0.5; b= bIn-0.5;
Quiet[{s, angle}=CoordinateTransform[{"Cartesian"->"Polar",2},{a,b}]/.Indeterminate->0,{ArcTan::indet}];
angle = angle-\[Theta]In-4 Pi/3 +2 Pi;h=angle/(2 Pi) ; s = Sqrt[2]*s; 
Hue[h,s,y]
];


LCaCbColor[yab_,\[Theta]_]:=Module[{y,a,b,h,s,angle},
If[TrueQ[LCaCbColorTheta==\[Theta]],LCaCbColorFast[yab[[1]],yab[[2]],yab[[3]]],
LCaCbColorFastTheta[yab[[1]],yab[[2]],yab[[3]],\[Theta]]]]


(* ::Subsubsection:: *)
(*3 D Cubes*)


LCaCbCubeFinite3D[\[Theta]_,fidelity_]:=Module[{},
SetUpLCaCbColor[\[Theta]];
{LCaCbColor[#,\[Theta]],Cuboid[#,#+1/(fidelity-1)]}&/@Tuples[Range[0,1,1/(fidelity-1)],3]
]


LCaCbAxisEnds3D[\[Theta]_,bri_:1]:=Module[{c1,c2,col},
c1=Transpose[cubeFaces[ LCaCbAxisRanges[\[Theta]]]];
c2=Transpose[cubeFacesInside[LCaCbAxisRanges[\[Theta]],0.001]];
col=Transpose[cubeFaces[{{0,1},{0,1},{0,1}}]];
col[[3,1]]=col[[3,1]]*bri;
col[[4,1]]=col[[4,1]]*bri;
col[[5,1]]=col[[5,1]]*bri;
col[[6,1]]=col[[6,1]]*bri;
Table[{Glow[LCaCbColor[col[[i]],\[Theta]]],Black,Cylinder[{c1[[i]],c2[[i]]},0.1]},{i,1,6}]
]


LCaCbCube3D[\[Theta]_]:=Module[{RGBinLCaCbcorners,RGBCubeCorners,LCaCbCubeCorners,LCaCbinRGBCubeCorners,faces,ranges},
RGBinLCaCbcorners = Transpose[RGBCube["LCaCb"][\[Theta]]];
RGBCubeCorners = Transpose[cubeCorners[{{0,1},{0,1},{0,1}}]];LCaCbCubeCorners =Transpose[cubeCorners[ LCaCbAxisRanges[\[Theta]]]];
LCaCbinRGBCubeCorners =Transpose[cubeCorners[ iLCaCb[\[Theta]]. cubeCorners[ LCaCbAxisRanges[\[Theta]]]]];
faces = {{1,2,3,4},{5,6,7,8},{1,2,7,6},{2,3,8,7},{3,4,5,8},{1,4,5,6}};
ranges = LCaCbAxisRanges[\[Theta]];
{Polygon[LCaCbCubeCorners[[faces[[1]]]], VertexColors->MapThread[LCaCbColor[{##},\[Theta]]&,Transpose[RGBCubeCorners[[faces[[1]]]]]]], 
 Polygon[LCaCbCubeCorners[[faces[[2]]]], VertexColors->MapThread[LCaCbColor[{##},\[Theta]]&,Transpose[RGBCubeCorners[[faces[[2]]]]]]], 
 Polygon[LCaCbCubeCorners[[faces[[3]]]], VertexColors->MapThread[LCaCbColor[{##},\[Theta]]&,Transpose[RGBCubeCorners[[faces[[3]]]]]]], 
 Polygon[LCaCbCubeCorners[[faces[[4]]]], VertexColors->MapThread[LCaCbColor[{##},\[Theta]]&,Transpose[RGBCubeCorners[[faces[[4]]]]]]],
 Polygon[LCaCbCubeCorners[[faces[[5]]]], VertexColors->MapThread[LCaCbColor[{##},\[Theta]]&,Transpose[RGBCubeCorners[[faces[[5]]]]]]],
 Polygon[LCaCbCubeCorners[[faces[[6]]]], VertexColors->MapThread[LCaCbColor[{##},\[Theta]]&,Transpose[RGBCubeCorners[[faces[[6]]]]]]]}
]


RGBinLCaCbCube3D[\[Theta]_]:=Module[{RGBinLCaCbcorners,RGBCubeCorners,LCaCbCubeCorners,LCaCbinRGBCubeCorners,faces,ranges},
RGBinLCaCbcorners = Transpose[RGBCube["LCaCb"][\[Theta]]];
RGBCubeCorners = Transpose[cubeCorners[{{0,1},{0,1},{0,1}}]];LCaCbCubeCorners =Transpose[cubeCorners[ LCaCbAxisRanges[\[Theta]]]];
LCaCbinRGBCubeCorners =Transpose[cubeCorners[ iLCaCb[\[Theta]]. cubeCorners[ LCaCbAxisRanges[\[Theta]]]]];
faces = {{1,2,3,4},{5,6,7,8},{1,2,7,6},{2,3,8,7},{3,4,5,8},{1,4,5,6}};
ranges = LCaCbAxisRanges[\[Theta]];
{Polygon[RGBinLCaCbcorners[[faces[[1]]]],VertexColors->MapThread[RGBColor,Transpose[RGBCubeCorners[[faces[[1]]]]]]], 
 Polygon[RGBinLCaCbcorners[[faces[[2]]]],VertexColors->MapThread[RGBColor,Transpose[RGBCubeCorners[[faces[[2]]]]]]], 
 Polygon[RGBinLCaCbcorners[[faces[[3]]]],VertexColors->MapThread[RGBColor,Transpose[RGBCubeCorners[[faces[[3]]]]]]],
 Polygon[RGBinLCaCbcorners[[faces[[4]]]],VertexColors->MapThread[RGBColor,Transpose[RGBCubeCorners[[faces[[4]]]]]]],
 Polygon[RGBinLCaCbcorners[[faces[[5]]]],VertexColors->MapThread[RGBColor,Transpose[RGBCubeCorners[[faces[[5]]]]]]],
 Polygon[RGBinLCaCbcorners[[faces[[6]]]],VertexColors->MapThread[RGBColor,Transpose[RGBCubeCorners[[faces[[6]]]]]]]}
]


Clear[RGBCubeInYabFinite];
RGBCubeInYabFinite[\[Theta]_,cut_:3,n_:8]:=Module[{cube},
  cube=Raster3D[Table[List[i,j,k,If[i+j+k<cut,1,0.03]],{k,0,1,1/n},{j,0,1,1/n},{i,0,1,1/n}],{{0,0,0},{1,1,1}},ColorFunction->RGBColor];
  Rotate[Rotate[Rotate[cube,Pi/4,{0,1,0}],-ArcTan[1/Sqrt[2]],{0,0,1}],\[Theta],{1,0,0}]
]


(*GraphicsCube[elem__,opts:OptionsPattern[GraphicsCube]]:=Graphics3D[elem, Flatten[{opts,
FilterRules[Options[GraphicsCube],Except[opts]]}]];
Options[GraphicsCube]=Evaluate[Options[Graphics3D]];
SetOptions[GraphicsCube,Lighting->"Neutral",PlotRange->All,Axes->True,ViewVertical->{1,0,0},AxesLabel->{"Luminocity","Chrom a", "Chrom b"}];*)


GraphicsCubeOpts=Sequence[Lighting->"Neutral",Axes->True,ViewVertical->{1,0,0},AxesLabel->{"Luminosity","Chrom a", "Chrom b"}];
GraphicsCubeOptions[opts:OptionsPattern[Graphics3D]]:=Module[{dfltOpts},
dfltOpts=Flatten[{GraphicsCubeOpts,FilterRules[Options[Graphics3D],Except[GraphicsCubeOpts]]}];
Flatten[{opts, FilterRules[dfltOpts,Except[opts]]}]
]


ShowLCaCbCube3D[\[Theta]_,opts:OptionsPattern[Graphics3D]]:=Module[{opt},
opt=GraphicsCubeOptions[opts, PlotRange->LCaCbAxisRanges[\[Theta]]];
Graphics3D[
Flatten[{Opacity[0.1],LCaCbCube3D[\[Theta]],Opacity[1],RGBinLCaCbCube3D[\[Theta]],LCaCbAxisEnds3D[-\[Theta]]}], opt]
]


LCaCbPolygon[\[Theta]_]:=Transpose[{Take[RGBCube["LCaCb"][\[Theta] ][[2]],{2,7}],Take[RGBCube["LCaCb"][\[Theta] ][[3]],{2,7}]}]


(* ::Subsection:: *)
(*Normalised LCaCb Cube*)


nLCaCbScale = Function[{\[Theta]},Evaluate[Simplify[1/LCaCbAxisLengths[\[Theta]]]]];


nLCaCb= Function[{\[Theta]},Evaluate[TrigReduce[nLCaCbScale[\[Theta]]  LCaCb[\[Theta]]]]];


inLCaCb= Function[{\[Theta]},Evaluate[TrigFactor[TrigReduce[FullSimplify[TrigExpand[Inverse[nLCaCb[\[Theta]]]]]]]]];


nLCaCbAxisRanges={{0,1},{-0.5 ,0.5},{-0.5 ,0.5}};


nLCaCbAxisLengths = {1,1,1};


RGBCube[nLCaCb]=Function[{\[Theta]},Evaluate[FullSimplify[nLCaCb[\[Theta]].RGBCube["RGB"]]]];
nLCaCbCube[nLCaCb]=cubeCorners[nLCaCbAxisRanges];
nLCaCbCube["RGB"]=Function[{\[Theta]},Evaluate[FullSimplify[inLCaCb[\[Theta]].nLCaCbCube[nLCaCb]]]];



nLCaCbPolygon= Function[{\[Theta]},Evaluate[Transpose[{Take[RGBCube[nLCaCb][\[Theta] ][[2]],{2,7}],Take[RGBCube[nLCaCb][\[Theta] ][[3]],{2,7}]}]]];


(* ::Section:: *)
(*General Utility *)


fracTicks[n_]:=List[Sequence@@Table[{N[-2^(-i)],-2^(-i)},{i,0,n}],Sequence@@Table[{N[2^(-i)],2^(-i)},{i,0,n}]]


MixTicks[ticks_,specialTicks_,margin_:6]:=Module[{posFun,pos},
posFun=Function[{x},Evaluate[Or@@Map[(#1-margin<x<#1+margin)&,specialTicks[[All,1]]]]];
pos=Position[ticks[[All,1]],_?posFun];
{Sequence@@Delete[ticks,pos],Sequence@@specialTicks}
]


FracTicks[min_,max_,n_:6,minMax:_:{0.01,0},color_:Black]:=Module[{m},
m=Max[Ceiling[Log2[max]],Ceiling[Log2[-min]]];
List[Sequence@@Table[{N[-2^(-i)],-2^(-i),minMax,color},{i,-m,n}],Sequence@@Table[{N[2^(-i)],2^(-i),minMax,color},{i,-m,n}]]
]


Clear[PiTicks]
PiTicks[min_,max_,n_:6,minMax:_:{0.01,0},color_:Black]:=Block[{s},
s= Floor[n Pi/(max-min)];
Table[{N[i Pi/s],(i "\[Pi]")/s, minMax, color},{i,Floor[s min/Pi],Ceiling[s max/Pi]}]]


BinaryTicks[min_,max_,m_:3]:=Module[{n,nn,mm},
mm=Ceiling[Log2[max-min]]-m;
Table[{i 2^(mm),i 2^(mm)},{i,Floor[min/2^(mm)],Ceiling[max/2^(mm)]}]
]


ApplyToPiecewise[func_,pwFunc_]:=Module[{posPi,pos},
posPi=Position[pwFunc,Piecewise];
If[Length[posPi]>=1,
pos =Table[Flatten[{Rest[posPi[[1]]],1,i,1}],{i,1,Length[pwFunc[[Sequence@@Rest[posPi[[1]]],1]]]}];
MapAt[func,pwFunc,pos],func[pwFunc]]]


nonNegativeSign[elem_]:=If[NonNegative[Simplify[elem]],1,-1]
SetAttributes[nonNegativeSign,Listable];


matSameSign[mat_]:=Module[{nn},nn=nonNegativeSign[mat];sameSign=Sign[nn.{1,1,1}]; (sameSign nn +1)/2];


Occurance[idx_,fun_:Flatten]:=Module[{min,max,occurCount,occur,pos,cnt},
min=Min[idx];
max=Max[idx];
occurCount=Table[i,{i,min,max}];
occur=Table[0,{i,1,Length[idx]}];
For[i=min,i<=max,i++,
pos=Flatten[Position[idx,i]];
cnt=Table[i,{i,1,Length[pos]}];
occur[[pos]]=fun[cnt];];
occur]


intersectionFromPoints[{p1_, p2_}, {p3_, p4_}] := 
{(p1[[1]]*(p4[[1]]*(-p2[[2]] + p3[[2]]) + p3[[1]]*(p2[[2]] - p4[[2]])) + p2[[1]]*(p4[[1]]*(p1[[2]] - p3[[2]]) + p3[[1]]*(-p1[[2]] + p4[[2]])))/
    (p4[[1]]*(p1[[2]] - p2[[2]]) + p3[[1]]*(-p1[[2]] + p2[[2]]) + (p1[[1]] - p2[[1]])*(p3[[2]] - p4[[2]])),(p4[[1]]*(p1[[2]] - p2[[2]])*p3[[2]] + p1[[1]]*p2[[2]]*p3[[2]] - p3[[1]]*p1[[2]]*p4[[2]] - p1[[1]]*p2[[2]]*p4[[2]] + p3[[1]]*p2[[2]]*p4[[2]] + 
     p2[[1]]*p1[[2]]*(-p3[[2]] + p4[[2]]))/(p4[[1]]*(p1[[2]] - p2[[2]]) + p3[[1]]*(-p1[[2]] + p2[[2]]) + (p1[[1]] - p2[[1]])*(p3[[2]] - p4[[2]]))}


eqnFromPoints[{x1_,y1_},{x2_,y2_}]:=Function[{x$},Evaluate[(x$ (-y1+y2))/(-x1+x2)+(-x2 y1+x1 y2)/(x1-x2)]];


ValueThumbSlider[v_] := ValueThumbSlider[Dynamic[v], {0, 1}]; 
ValueThumbSlider[Dynamic[var_], {min_, max_}, options___] := LocatorPane[Dynamic[If[ !NumberQ[var], var = min]; {var, 0}, 
     (var = First[#1]) & ], Graphics[{AbsoluteThickness[1.5], Line[{{min, 0}, {max, 0}}], 
      Dynamic[{Text[var, {var, 0}, {0, -1}], Polygon[{Offset[{0, -1}, {var, 0}], Offset[{-5, -8}, {var, 0}], 
          Offset[{5, -8}, {var, 0}]}]}]}, ImageSize -> {300, 30}, PlotRange -> {{min, max} + 0.1*{-1, 1}*(max - min), {-1, 1}}, 
     AspectRatio -> 1/10], {{min, 0}, {max, 0}}, Appearance -> None]; 
ValueThumbSlider[Dynamic[var_], {min_, max_, scale_}, options___] := 
   LocatorPane[Dynamic[If[ !NumberQ[var], var = min]; {var, 0}, (var = First[#1]) & ], 
    Graphics[{AbsoluteThickness[1.5], Line[{{min, 0}, {max, 0}}], Dynamic[{Text[var, {var, 0}, {0, -1}], 
        Polygon[{Offset[{0, -1}, {var, 0}], Offset[{-5, -8}, {var, 0}], Offset[{5, -8}, {var, 0}]}]}]}, ImageSize -> {300, 30}, 
     PlotRange -> {{min, max} + 0.1*{-1, 1}*(max - min), {-1, 1}}, AspectRatio -> 1/10], {{min, 0}, {max, 0}, {scale, 0}}, 
    Appearance -> None]; 




Clear[sliderIndicatorPoint];
sliderIndicatorPoint[var_]:=Graphics[{Dynamic[{Text[var, {var, 0}, {0, -1}], Polygon[{Offset[{0, -1}, {var, 0}], Offset[{-5, -8}, {var, 0}], 
          Offset[{5, -8}, {var, 0}]}],Text[StringReplace[SymbolName[Unevaluated[var]],"$$"~~x:DigitCharacter..->""], Offset[{0, -9}, {var, 0}], {0, 1}]}]}]
SetAttributes[sliderIndicatorPoint,HoldAllComplete]

SetAttributes[ValueThumbSlider,HoldFirst];
ValueThumbSlider[{varsIn__}, {min_,max_}, options___] := Module[{in,ranges,appearance,vars},
setUnset[min,varsIn,max];
vars=Map[SymbolName,{ReleaseHold[Map[Unevaluated,Hold[varsIn]]]}];
in = Map[StringJoin[{"List[",#,",0]"}]&,vars];
ranges=List[
StringJoin[{"List[{",ToString[min],",0}, {Dynamic[",vars[[1+1]],"],0}]"}],
Sequence@@Table[
StringJoin[{"List[{Dynamic[",vars[[i-1]],"],0}, {Dynamic[",vars[[i+1]],"],0}]"}]
,{i,2,Length[vars]-1}],
StringJoin["List[{Dynamic[",vars[[Length[vars]-1]],"],0}, {",ToString[max],",0}]"]];
appearance = Map[StringJoin[{"Dynamic[sliderIndicatorPoint[",#,"]]"}]&,vars];
riff[list_]:=StringJoin["List[",Riffle[list,", "],"]"];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",riff[in],"], Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, 
     AspectRatio -> 30/Scaled[1]],",riff[ranges],", Appearance -> ",riff[appearance],"]"}]]
]

ValueThumbSlider[{varsIn__}, {min_,max_,scale_}, options___] := Module[{in,ranges,appearance},
setUnset[min,varsIn,max];
vars=Map[SymbolName,{ReleaseHold[Map[Unevaluated,Hold[varsIn]]]}];
in = Map[StringJoin[{"List[",#,",0]"}]&,vars];
ranges=List[
StringJoin[{"List[{",ToString[min],",0}, {Dynamic[",vars[[1+1]],"],0}, {",ToString[scale],",0}]"}],
Sequence@@Table[
StringJoin[{"List[{Dynamic[",vars[[i-1]],"],0}, {Dynamic[",vars[[i+1]],"],0}, {",ToString[scale],",0}]"}]
,{i,2,Length[vars]-1}],
StringJoin["List[{Dynamic[",vars[[Length[vars]-1]],"],0}, {",ToString[max],",0}, {",ToString[scale],",0}]"]];
appearance = Map[StringJoin[{"Dynamic[sliderIndicatorPoint[",#,"]]"}]&,vars];
riff[list_]:=StringJoin["List[",Riffle[list,", "],"]"];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",riff[in],"], Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, 
     AspectRatio -> 30/Scaled[1]],",riff[ranges],", Appearance -> ",riff[appearance],"]"}]]
]

ValueThumbSlider[{varsIn_}, {min_, max_}, options___] := Module[{in,ranges,appearance},
setUnset[min,varsIn,max];
vars=SymbolName[Unevaluated[varsIn]];
in = StringJoin[{"List[",vars,",0]"}];
ranges= StringJoin[{"List[{",ToString[min],",0}, {Dynamic[",ToString[max],"],0}]"}];
appearance = StringJoin[{"Dynamic[sliderIndicatorPoint[",ToString[vars],"]]"}];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",in,"], 
Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, 
     AspectRatio -> 30/Scaled[1]],",ranges,", Appearance -> ",appearance,"]"}]]
]

ValueThumbSlider[{varsIn_}, {min_, max_,scale_}, options___] := Module[{in,ranges,appearance},
setUnset[min,varsIn,max];
vars=SymbolName[Unevaluated[varsIn]];
in = StringJoin[{"List[",vars,",0]"}];
ranges= StringJoin[{"List[{",ToString[min],",0}, {Dynamic[",ToString[max],"],0}, {",ToString[scale],",0}]"}];
appearance = StringJoin[{"Dynamic[sliderIndicatorPoint[",ToString[vars],"]]"}];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",in,"], 
Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, 
     AspectRatio -> 30/Scaled[1]],",ranges,", Appearance -> ",appearance,"]"}]]
]


Clear[sliderIndicatorPoint];
sliderIndicatorPoint[var_]:=Graphics[{Dynamic[{Text[var, {var, 0}, {0, -1}], Polygon[{Offset[{0, -1}, {var, 0}], Offset[{-5, -8}, {var, 0}], 
          Offset[{5, -8}, {var, 0}]}],Text[StringReplace[SymbolName[Unevaluated[var]],"$$"~~x:DigitCharacter..->""], Offset[{0, -9}, {var, 0}], {0, 1}]}]}]
SetAttributes[sliderIndicatorPoint,HoldAllComplete]

Clear[ValueThumbSlider];
ValueThumbSlider[{varsIn__}, {min_,max_}, options___] := Module[{in,ranges,appearance,heldVarsIn,heldVars,dynamic,dynVars,vars},
heldVarsIn={ReleaseHold[Map[Hold,Map[Unevaluated,Hold[varsIn]]]]};
heldVars=heldVarsIn/.Dynamic[sym_,bla___]->sym;
dynamic=Map[(TrueQ[#[[1,1,0]]==Dynamic])&,heldVarsIn];
dynVars=Table[If[dynamic[[i]],ToString[#]&[ReleaseHold[heldVarsIn[[i]]] ],StringJoin["Dynamic[",ToString[#]&[ReleaseHold[heldVars[[i]]]],"]"]],{i,1,Length[dynamic]}];
vars=Map[ToString,Map[ReleaseHold,heldVars]];
ToExpression[StringJoin["setUnset[",Riffle[{ToString[min],Sequence@@vars,ToString[max]},", "],"]"]];
in = Map[StringJoin[{"List[",#,",0]"}]&,dynVars];
ranges=List[
StringJoin[{"List[{",ToString[min],",0}, {",dynVars[[1+1]],",0}]"}],
Sequence@@Table[
StringJoin[{"List[{",dynVars[[i-1]],",0}, {",dynVars[[i+1]],",0}]"}]
,{i,2,Length[dynVars]-1}],
StringJoin["List[{",vars[[Length[vars]-1]],",0}, {",ToString[max],",0}]"]];
appearance = Map[StringJoin[{"Dynamic[sliderIndicatorPoint[",#,"]]"}]&,vars];
riff[list_]:=StringJoin["List[",Riffle[list,", "],"]"];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",riff[in],"], Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, AspectRatio -> 30/Scaled[1]],",riff[ranges],", Appearance -> ",riff[appearance],"]"}]]
]

ValueThumbSlider[{varsIn_}, {min_,max_}, options___] := Module[{in,ranges,appearance,heldVarsIn,heldVars,dynamic,dynVars,vars},
heldVarsIn=Hold[Unevaluated[varsIn]];
heldVars=heldVarsIn/.Dynamic[sym_,bla___]->sym;
dynamic=TrueQ[heldVarsIn[[1,1,0]]==Dynamic];
dynVars=If[dynamic,ToString[#]&[ReleaseHold[heldVarsIn] ],StringJoin["Dynamic[",ToString[#]&[ReleaseHold[heldVars]],"]"]];
vars=ToString[#]&[ReleaseHold[heldVars]];
ToExpression[StringJoin["setUnset[",Riffle[{ToString[min],vars,ToString[max]},", "],"]"]];
in = StringJoin[{"List[",dynVars,",0]"}];
ranges=StringJoin[{"List[{",ToString[min],",0}, {",ToString[max],",0}]"}];
appearance = StringJoin[{"Dynamic[sliderIndicatorPoint[",vars,"]]"}];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",in,"], Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, AspectRatio -> 30/Scaled[1]],",ranges,", Appearance -> ",appearance,"]"}]]
]


ValueThumbSlider[{varsIn_}, {min_,max_,scale_}, options___] := Module[{in,ranges,appearance,heldVarsIn,heldVars,dynamic,dynVars,vars},
heldVarsIn=Hold[Unevaluated[varsIn]];
heldVars=heldVarsIn/.Dynamic[sym_,bla___]->sym;
dynamic=TrueQ[heldVarsIn[[1,1,0]]==Dynamic];
dynVars=If[dynamic,ToString[#]&[ReleaseHold[heldVarsIn] ],StringJoin["Dynamic[",ToString[#]&[ReleaseHold[heldVars]],"]"]];
vars=ToString[#]&[ReleaseHold[heldVars]];
ToExpression[StringJoin["setUnset[",Riffle[{ToString[min],vars,ToString[max]},", "],"]"]];
in = StringJoin[{"List[",dynVars,",0]"}];
ranges=StringJoin[{"List[{",ToString[min],",0}, {",ToString[max],",0}, {",ToString[scale],",0}]"}];
appearance = StringJoin[{"Dynamic[sliderIndicatorPoint[",vars,"]]"}];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",in,"], Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, AspectRatio -> 30/Scaled[1]],",ranges,", Appearance -> ",appearance,"]"}]]
]

ValueThumbSlider[{varsIn__}, {min_,max_,scale_}, options___] := Module[{in,ranges,appearance,heldVarsIn,heldVars,dynamic,dynVars,vars},
heldVarsIn={ReleaseHold[Map[Hold,Map[Unevaluated,Hold[varsIn]]]]};
heldVars=heldVarsIn/.Dynamic[sym_,bla___]->sym;
dynamic=Map[(TrueQ[#[[1,1,0]]==Dynamic])&,heldVarsIn];
dynVars=Table[If[dynamic[[i]],ToString[#]&[ReleaseHold[heldVarsIn[[i]]] ],StringJoin["Dynamic[",ToString[#]&[ReleaseHold[heldVars[[i]]]],"]"]],{i,1,Length[dynamic]}];
vars=Map[ToString,Map[ReleaseHold,heldVars]];
ToExpression[StringJoin["setUnset[",Riffle[{ToString[min],Sequence@@vars,ToString[max]},", "],"]"]];
in = Map[StringJoin[{"List[",#,",0]"}]&,dynVars];
ranges=List[
StringJoin[{"List[{",ToString[min],",0}, {",dynVars[[1+1]],",0}, {",ToString[scale],",0}]"}],
Sequence@@Table[
StringJoin[{"List[{",dynVars[[i-1]],",0}, {",dynVars[[i+1]],",0}, {",ToString[scale],",0}]"}]
,{i,2,Length[dynVars]-1}],
StringJoin["List[{",vars[[Length[vars]-1]],",0}, {",ToString[max],",0}, {",ToString[scale],",0}]"]];
appearance = Map[StringJoin[{"Dynamic[sliderIndicatorPoint[",#,"]]"}]&,vars];
riff[list_]:=StringJoin["List[",Riffle[list,", "],"]"];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",riff[in],"], Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, AspectRatio -> 30/Scaled[1]],",riff[ranges],", Appearance -> ",riff[appearance],"]"}]]
]



Clear[ValueThumbSlider]
ValueThumbSlider[Dynamic[{varsIn__},func_], {min_,max_,scale___}, options___] := Module[{},
function=StringReplace[ToString[Unevaluated[func],InputForm],"#"~~x:DigitCharacter..:> "#"~~"[["~~x~~",1]]" ];
heldVars={ReleaseHold[Map[Hold,Map[Unevaluated,Hold[varsIn]]]]}/.Dynamic[sym_,bla___]->sym;
     vars=Map[ToString,Map[ReleaseHold,heldVars]];
ToExpression[StringJoin["setUnset[",Riffle[{ToString[min],Sequence@@vars,ToString[max]},", "],"]"]];
    in = Map[StringJoin[{"List[",#,",0]"}]&,vars];
scle=If[TrueQ[scale==Null],"",StringJoin[{", {",ToString[scale],",0}"}]];
ranges=List[
StringJoin[{"List[{",ToString[min],",0}, {Dynamic[",vars[[1+1]],"],0}",scle,"]"}],
Sequence@@Table[
StringJoin[{"List[{Dynamic[",vars[[i-1]],"],0}, {Dynamic[",vars[[i+1]],"],0}",scle,"]"}]
,{i,2,Length[vars]-1}],
StringJoin["List[{Dynamic[",vars[[Length[vars]-1]],"],0}, {",ToString[max],",0}",scle,"]"]];
appearance = Map[StringJoin[{"Dynamic[sliderIndicatorPoint[",#,"]]"}]&,vars];
riff[list_]:=StringJoin["List[",Riffle[list,", "],"]"];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",riff[in],", ",function,"], Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, AspectRatio -> 30/Scaled[1]],",riff[ranges],", Appearance -> ",riff[appearance],"]"}]]
]

ValueThumbSlider[Dynamic[{varsIn_},func_], {min_,max_,scale___}, options___] := Module[{},
function=StringReplace[ToString[Unevaluated[func],InputForm],"#"~~x:DigitCharacter..:> "#"~~"[["~~x~~"]]" ];
     vars=ToString[Unevaluated[varsIn]];
ToExpression[StringJoin["setUnset[",Riffle[{ToString[min],vars,ToString[max]},", "],"]"]];
    in = StringJoin[{"List[",vars,",0]"}];
scle=If[TrueQ[scale==Null],"",StringJoin[{", {",ToString[scale],",0}"}]];
ranges= StringJoin[{"List[{",ToString[min],",0}, {",ToString[max],",0}",scle,"]"}];
appearance = StringJoin[{"Dynamic[sliderIndicatorPoint[",vars,"]]"}];
ToExpression[StringJoin[{"LocatorPane[Dynamic[",in,", ",function,"], Graphics[{AbsoluteThickness[1.5], Line[{{",ToString[min],", 0}, {",ToString[max],", 0}}]}, ImageSize -> {Scaled[1],30}, PlotRange -> {{",ToString[min],"," ,ToString[max],"} + 0.1*{-1, 1}*(",ToString[max]," - ",ToString[min],"), {-12,8}}, AspectRatio -> 30/Scaled[1]],",ranges,", Appearance -> ",appearance,"]"}]]
]


findUnset[vars__]:=Module[{posSym,posNum,start,end},
posSym=Position[{vars},_Symbol,{1},Heads->False][[All,1]];
If[Length[posSym]>0,
posNum=Position[{vars},_Real|_Integer,{1},Heads->False][[All,1]];
start=Intersection[Union[posNum+1],posSym];
If[posSym[[1]]==1,PrependTo[start,1]];
end=Intersection[Union[posNum-1],posSym];
If[posSym[[-1]]==Length[{vars}],AppendTo[end,Length[{vars}]]];
Transpose[{start, end}]
,
{}]
]

SetAttributes[setUnset,HoldAll];
setUnset[minIn_,vars__,maxIn_]:=Module[{n,ends,newSequence,range,min,max},
newSequence=findUnset[minIn,vars,maxIn];
If[Length[newSequence]>0,
If[newSequence[[1,1]]==1,min={minIn,vars,maxIn}[[newSequence[[1,2]]+1]]-1,min=minIn];
If[newSequence[[-1,2]]==Length[{minIn,vars,maxIn}],max={minIn,vars,maxIn}[[newSequence[[-1,1]]-1]]+1,max=maxIn];
Do[
n=pos[[2]]-pos[[1]]+1;
ends=List[min,minIn,vars,maxIn,max][[pos+{0,2}]];
range=Range[Sequence@@ends,(ends[[2]]-ends[[1]])/(n+1)][[2;;n+1]];
Evaluate[List[minIn,vars,maxIn][[Span@@pos]]] = N[range]
,{pos,newSequence}]
]
]


Clear[ LabelPoint];
LabelPoint[x_,fun_,txt_:"",color_:Green,align_:{0,0},size_:12]:=Block[{pnt,text},
pnt=Round[N[{x,fun[x]}]];
If[TrueQ[txt==""],
  text=StringJoin[ToString[pnt[[1]]],"  ",ToString[pnt[[2]]]],
  text=txt];
{color,Opacity[0.6],Disk[pnt,size],Black,Opacity[1],Text[text,pnt,align]}];

Clear[ LabelPointGrad];
 LabelPointGrad[x_,fun_,txt_:"",color_:Green,align_:{0,0},len_:40,size_:12]:=Block[{pnt,text,m,line,theta},
pnt=Round[N[{x,fun[x]}]];
m=Function[{xx},Evaluate[D[fun[xx],xx]]];
theta=ArcTan[m[x]];
line=Function[{xx},Evaluate[ {xx Cos[theta], xx Sin[theta]} + pnt ]];
If[TrueQ[txt==""],text=StringJoin[ToString[pnt[[1]]],"  ",ToString[pnt[[2]]]],text=txt];{color,Opacity[0.6],
Disk[pnt,size],Disk[line[len],size/2],Disk[line[-len], size/2],
Thick,Line[{line[-len],line[len]}],
Black,Opacity[1],
Text[text,pnt,align,line[len]-line[-len]],Text[ToString[NumberForm[N[m[x]],3]],line[len],{0,0},line[len]-line[-len]],
Text[ToString[NumberForm[N[m[x]],3]],line[-len],{0,0},line[len]-line[-len]]}];



Clear[toPosCircle,toNegPosCircle]
toPosCircle[\[Theta]_?((-64Pi<# <64Pi)&)]:=Mod[(\[Theta]+2Pi),2Pi];
Format[toPosCircle[\[Theta]_],TraditionalForm]:=\[Theta];
toNegPosCircle[\[Theta]_?((-64Pi<# <64Pi)&)]:= If[Mod[(\[Theta]+2Pi),2Pi]>=Pi,Mod[(\[Theta]+2Pi),2Pi]-2Pi,Mod[(\[Theta]+2Pi),2Pi]];Format[toNegPosCircle[\[Theta]_],TraditionalForm]:=\[Theta];

posCircularInequality[a_?((0<= # <= 2Pi)&), relA_, \[Theta]_?((-2Pi<= # <= 2Pi)&), relB_,b_?((0<= # <= 2Pi)&)]:=Inequality[a, relA, toPosCircle[\[Theta]], relB,b];
Format[posCircularInequality[a_, relA_, \[Theta]_, relB_,b_],TraditionalForm]:=Inequality[a, relA, \[Theta], relB,b];
Format[posCircularInequality[a_, relA_, \[Theta]_, relB_,b_],TeXForm]:=TeXForm[Inequality[a, relA, \[Theta], relB,b]];negPosCircularInequality[a_?((-Pi<= # <=Pi)&), relA_, \[Theta]_?((-64Pi<# <64Pi)&), relB_,b_?((-Pi<= # <=Pi)&)]:=Inequality[a, relA, toNegPosCircle[\[Theta]], relB,b];
Format[negPosCircularInequality[a_, relA_, \[Theta]_, relB_,b_],TraditionalForm]:=Inequality[a, relA, \[Theta], relB,b];
Format[negPosCircularInequality[a_, relA_, \[Theta]_, relB_,b_],TeXForm]:=TeXForm[Inequality[a, relA, \[Theta], relB,b]]

Clear[CircularInequality,circularInequality]; 
CircularInequality[a_, Greater,      x_, Greater,      b_,opts:OptionsPattern[]] := CircularInequality[b, Less,      x, Less,      a, opts]
CircularInequality[a_, Greater,      x_, GreaterEqual, b_,opts:OptionsPattern[]] := CircularInequality[b, LessEqual, x, Less,      a, opts]
CircularInequality[a_, GreaterEqual, x_, Greater,      b_,opts:OptionsPattern[]] := CircularInequality[b, Less,      x, LessEqual, a, opts]
CircularInequality[a_, GreaterEqual, x_, GreaterEqual, b_,opts:OptionsPattern[]] := CircularInequality[b, LessEqual, x, LessEqual, a, opts]
Options[CircularInequality]={Range->"Automatic"}; (* Range->"Automatic"|"Positive"|"Mixed"*)
CircularInequality::range="The range `1` is not \"Automatic\", \"Positive\" or \"Mixed\".";
CircularInequality[a_, relA:(Less|LessEqual), \[Theta]_, relB:(Less|LessEqual), b_,opts:OptionsPattern[]] := 
  Module[{a02, a11, b02, b11, out}, 
a02 = toPosCircle[a]; b02 = toPosCircle[b]; 
a11 = toNegPosCircle[a]; b11 = toNegPosCircle[b]; 
  incZero =  Not[Inequality[a02, LessEqual, b02]]; 
Switch[OptionValue[Range],
"Automatic", If[incZero, 
out = negPosCircularInequality[a11, relA, \[Theta], relB, b11], 
out = posCircularInequality[a02, relA, \[Theta], relB, b02]
], 
"Positive", If[incZero, 
out = posCircularInequality[a02, relA, \[Theta], Less, 2 Pi]||posCircularInequality[0, LessEqual, \[Theta], relB, b02], 
out = posCircularInequality[a02, relA, \[Theta], relB, b02]
], 
"Mixed", If[incZero, 
out = negPosCircularInequality[a11, relA, \[Theta], relB, b11], 
out = negPosCircularInequality[-Pi, LessEqual, \[Theta], relA, b11]||negPosCircularInequality[a11, relB, \[Theta], LessEqual, Pi]
],
 _, Message[CircularInequality::range, OptionValue[Range]]; 
      If[incZero, out = negPosCircularInequality[a11, relA, \[Theta], relB, b11], out = posCircularInequality[a02, relA, \[Theta], relB, b02]]];
 out];
Format[CircularInequality[a_, relA_, \[Theta]_, relB_, b_],TraditionalForm] := TraditionalForm[Inequality[a, relA, \[Theta], relB, b]];
Format[CircularInequality[a_, relA_, \[Theta]_, relB_, b_],TeXForm]:=TeXForm[Inequality[a, relA, \[Theta], relB, b]];



(* ::Text:: *)
(*Usage*)


(*i=2;*)
(*{TraditionalForm[CircularInequality[(i-6) Pi/6, LessEqual, \[Theta], Less,i Pi/6,Range->"Automatic"]],*)
(*TraditionalForm[CircularInequality[(i-6) Pi/6, LessEqual, \[Theta], Less,i Pi/6,Range->"Positive"]],*)
(*TraditionalForm[CircularInequality[(i-6) Pi/6, LessEqual, \[Theta], Less,i Pi/6,Range->"Mixed"]]}*)
(**)
(*i=9;*)
(*{TraditionalForm[CircularInequality[(i-6) Pi/6, LessEqual, \[Theta], Less,i Pi/6,Range->"Automatic"]],*)
(*TraditionalForm[CircularInequality[(i-6) Pi/6, LessEqual, \[Theta], Less,i Pi/6,Range->"Positive"]],*)
(*TraditionalForm[CircularInequality[(i-6) Pi/6, LessEqual, \[Theta], Less,i Pi/6,Range->"Mixed"]]}*)
(**)
(*TraditionalForm[{CircularInequality[(2-6) Pi/6, LessEqual, Pi/6, Less,2 Pi/6],*)
(*CircularInequality[(2-6) Pi/6, LessEqual, -Pi/6, Less,2 Pi/6],CircularInequality[(2-6) Pi/6, LessEqual, 11 Pi/6, Less,2 Pi/6]}]*)


(* ::Section:: *)
(*Text Display*)


MatrixFormCubeColor[mat_,forgroundWhite_:1,backgroundWhite_:1]:=Module[{fg,bg },fg = forgroundWhite; bg={backgroundWhite,backgroundWhite-1};MatrixForm[{
MapThread[Style[#1,#2,Background->#3]&, {mat[[1]],Map[RGBColor,fg Transpose[RGBCube["RGB"]]],Map[RGBColor,bg[[1]]-bg[[2]] Transpose[RGBCube["RGB"]]]}],MapThread[Style[#1,#2,Background->#3]&, {mat[[2]],Map[RGBColor,fg Transpose[RGBCube["RGB"]]],Map[RGBColor,bg[[1]]-bg[[2]] Transpose[RGBCube["RGB"]]]}],MapThread[Style[#1,#2,Background->#3]&, {mat[[3]],Map[RGBColor,fg Transpose[RGBCube["RGB"]]],Map[RGBColor,bg[[1]]-bg[[2]] Transpose[RGBCube["RGB"]]]}]}]]


colorMat[mat_]:=Module[{pos,out}, 
pos=Position[Sign[mat],1];out=MapAt[Style[#,Red]&,mat,pos]; 
pos=Position[Sign[mat],-1];out=MapAt[Style[#,Blue]&,out,pos];
pos=Position[matSameSign[mat],1];out=MapAt[Framed[#]&,out,pos];
 out];


mForm[mat_]:=ToString[MatrixForm[mat],TraditionalForm];


Clear[partShow];
partShow[Interpretation[_,pFun_],2]:=partShow[pFun];
partShow[Interpretation[pFun_,_],1]:=partShow[pFun];
partShow[Interpretation[pFun_,_]]:=partShow[pFun];
partShow[Piecewise[pFun_,_]]:=Module[{list},
  list=MapThread[partShowEx,{pFun,{Red,Green,Blue,Yellow,Orange,Cyan,Magenta,Pink,Brown,Purple,LightRed,LightGreen,LightBlue,LightYellow,LightOrange,LightCyan,LightMagenta,LightPink,LightBrown,LightPurple}[[1;;Length[pFun]]]}];
  Show[Flatten[list]]
];

partShowEx[List[fun_,Or[f_,l__]],color_:Blue]:={partShowEx[{fun,f},color],partShowEx[{fun,Or[l]},color]}
partShowEx[List[fun_,Or[f_]],    color_:Blue]:=partShowEx[{fun,f},color]
partShowEx[List[fun_,Or[f_]],    color_:Blue]:=partShowEx[{fun,f},color]

partShowEx[List[fun_,ineq:(Less| Greater| LessEqual|GreaterEqual)[l_,sym_,u_]],color_:Blue] := partDisp[
  ToString[fun,TraditionalForm], l, u, Function[{x,y,\[Theta],r},Evaluate[Head[ineq][l,\[Theta],u]]], PlotStyle->{color}]
partShowEx[List[fun_,ineq:(Inequality|circularInquality|posCircularInequality|negPosCircularInequality)[l_,ineql_,sym_,ineqr_,u_]],color_:Blue] := partDisp[
  ToString[fun,TraditionalForm], l, u, Function[{x,y,\[Theta],r},Evaluate[Inequality[l,ineql,\[Theta],ineqr,u]]], PlotStyle->{color}]


Protect[OuterLables];
ClearAll[partDisp];
Options[partDisp]={PlotStyle->{Blue},OuterLables->{True,False}};
partDisp[txt_,l_,u_,regionFun_,OptionsPattern[]]:=ParametricPlot[
{r Cos[\[Theta]],r Sin[\[Theta]]},{\[Theta],Min[0,l],Max[2 Pi,u]},{r,1/4,0.9},
RegionFunction->regionFun,
Mesh->None, FrameTicks->None,Frame->False,AspectRatio->1,PlotRangeClipping->False,ImageMargins-> 1,ImagePadding->1.1,
PlotStyle->OptionValue[PlotStyle],
PlotRange-> 1.2,
PlotLegends->{
  Placed[txt,{0.3 Cos[(l+u)/2]+0.5,0.3 Sin[(l+u)/2]+0.5}],
  If[TrueQ[OptionValue[OuterLables][[1]]],Placed[l,{ImageScaled[{0.4 Cos[l]+0.5,0.4 Sin[l]+0.5}],{-0.5 Cos[l]+0.5,-0.5 Sin[l]+0.5}}],Unevaluated[Sequence[]]],
  If[TrueQ[OptionValue[OuterLables][[2]]],Placed[u,{ImageScaled[{0.4 Cos[u]+0.5,0.4 Sin[u]+0.5}],{-0.5 Cos[u]+0.5,-0.5 Sin[u]+0.5}}],Unevaluated[Sequence[]]]
},
Axes->False]


(* ::Section:: *)
(*Graphics Display*)


numDisk[{{x_,y_},{indxA_,indxB_},{occA_,occB_}}]:={Orange,Disk[{x,y},Scaled[{0.02, 0.02}]],Blue,Text[{occA,occB},{x,y}]}


numDisk[{{x_,y_},num_}]:={Orange,Disk[{x,y},Scaled[{0.02, 0.02}]],Blue,Text[num,{x,y}]}


Clear[LabeldRectangle]
LabeldRectangle[x_List,y_List,expr_, offset:{_,_}:{0,0}, dir:{_,_}:{1,0}, margin_:0.9,color_:Blue]:=Module[{center,shift,txtPos},
center={Plus@@x/2,Plus@@y/2};
shift={margin (x[[2]]-x[[1]])/2,margin (y[[2]]-y[[1]])/2};
txtPos=center+  offset shift;
{color,Rectangle[{x[[1]],y[[1]]},{x[[2]],y[[2]]}],Opacity[1],Darker[color,0.8],Text[ expr, txtPos, offset, dir]}
]


CheckerBoardFromList[x_,y_,color_:Null,text_:Null, offset:{_,_}:{0,0}, dir:{_,_}:{1,0}, margin_:0.9]:=Module[{clr,txt,txtPos},
If[TrueQ[color==Null],clr=Table[ColorData[1][i j],{i,1,Length[x]-1,1},{j,1,Length[y]-1,1}],clr=color];
If[TrueQ[text==Null],
If[Length[y]>2&&Length[x]>2,
txt=Table[{i,j},{i,1,Length[x]-1,1},{j,1,Length[y]-1,1}],
txt=Table[i j,{i,1,Length[x]-1,1},{j,1,Length[y]-1,1}]],
txt=text];
Table[LabeldRectangle[{x[[i]],x[[i+1]]}, {y[[j]],y[[j+1]]}, txt[[i,j]], offset, dir, margin, clr[[i,j]]],{i,1,Length[x]-1,1},{j,1,Length[y]-1,1}]
]


plotRegionsFromList[t_,color_:Blue,opacity_:0.6,text_:Null,yRange_:{0,2},opts:OptionsPattern[]]:=Module[{r,txt,txtPos},
txtPos=0.9 (yRange[[2]]-yRange[[1]])+ yRange[[1]];
If[TrueQ[text==Null],txt=Table[i,{i,1,Length[t]}],txt=text];
r=Table[{Opacity[opacity],color,Rectangle[{t[[i]],yRange[[1]]},{t[[i+1]],yRange[[2]]}],Opacity[1],Darker[color],Text[txt[[i]],{(t[[i+1]]+t[[i]])/2,txtPos}]},{i,1,Length[t]-1,2}];
Graphics[r,opts]]


Options[legendMaker] = 
  Join[FilterRules[Options[Framed], 
    Except[{ImageSize, FrameStyle, Background, RoundingRadius, 
      ImageMargins}]], {FrameStyle -> None, 
    Background -> Directive[Opacity[.7], LightGray], 
    RoundingRadius -> 10, ImageMargins -> 0, PlotStyle -> Automatic, 
    PlotMarkers -> None, "LegendLineWidth" -> 35, 
    "LegendLineAspectRatio" -> .3, "LegendMarkerSize" -> 8, 
    "LegendGridOptions" -> {Alignment -> Left, Spacings -> {.4, .1}}}];


legendMaker::usage = 
  "Create a Graphics object with legends given by the list passed as \
the first argument. The options specify any non-deafult line styles \
(using PlotStyle -> {...}) or plot markers (using PlotMarkers -> \
{...}). For more options, inspect Options[legendMaker]";

legendMaker[textLabels_, opts : OptionsPattern[]] := 
  Module[{f, lineDirectives, markerSymbols, n = Length[textLabels], 
    x}, lineDirectives = ((PlotStyle /. {opts}) /. 
       PlotStyle | Automatic :> Map[ColorData[1], Range[n]]) /. 
     None -> {None};
   markerSymbols = 
    Replace[((PlotMarkers /. {opts}) /. 
         Automatic :> (Drop[
              Normal[ListPlot[Transpose[{Range[3]}], 
                  PlotMarkers -> Automatic][[1, 2]]][[1]], -1] /. 
             Inset[x_, i__] :> x)[[All, -1]]) /. {Graphics[gr__], 
         sc_} :> Graphics[gr, 
         ImageSize -> ("LegendMarkerSize" /. {opts} /. 
             Options[legendMaker, 
              "LegendMarkerSize"] /. {"LegendMarkerSize" -> 8})], 
      PlotMarkers | None :> 
       Map[Style["", Opacity[0]] &, textLabels]] /. 
     None | {} -> Style["", Opacity[0]];
   lineDirectives = PadRight[lineDirectives, n, lineDirectives];
   markerSymbols = PadRight[markerSymbols, n, markerSymbols];
   f = Grid[
     MapThread[{Graphics[{#1 /. None -> {}, 
          If[#1 === {None} || (PlotStyle /. {opts}) === None, {}, 
           Line[{{-.1, 0}, {.1, 0}}]], 
          Inset[#2, {0, 0}, Background -> None]}, 
         AspectRatio -> ("LegendLineAspectRatio" /. {opts} /. 
             Options[legendMaker, 
              "LegendLineAspectRatio"] /. {"LegendLineAspectRatio" -> \
.2}), ImageSize -> ("LegendLineWidth" /. {opts} /. 
             Options[legendMaker, 
              "LegendLineWidth"] /. {"LegendLineWidth" -> 35}), 
         ImagePadding -> {{1, 1}, {0, 0}}], 
        Text[#3, FormatType -> TraditionalForm]} &, {lineDirectives, 
       markerSymbols, textLabels}], 
     Sequence@
      Evaluate[("LegendGridOptions" /. {opts} /. 
          Options[legendMaker, 
           "LegendGridOptions"] /. {"LegendGridOptions" -> {Alignment \
-> Left, Spacings -> {.4, .1}}})]];
   Framed[f, 
    FilterRules[{Sequence[opts, Options[legendMaker]]}, 
     FilterRules[Options[Framed], Except[ImageSize]]]]];

extractStyles::usage = "returns a tuple {\"all line style \
directives\", \"all plot markers\"} found in the plot, in the order \
they are drawn. The two sublists need not have the same length if \
some lines don't use markers "; 
extractStyles[plot_] := 
 Module[{lines, markers, points, 
   extract = First[Normal[plot]]},(*In a plot,
  the list of lines contains no insets,so I use this to find it:*)
  lines = 
   Select[Cases[Normal[plot], {___, _Line, ___}, Infinity], 
    FreeQ[#1, Inset] &];
  points = 
   Select[Cases[Normal[plot], {___, _Point, ___}, Infinity], 
    FreeQ[#1, Inset] &];
  (*Most plot markers are inside Inset,
  except for Point in list plots:*)
  markers = Select[extract, ! FreeQ[#1, Inset] &];
  (*The function returns a list of lists:*){(*The first return value \
is the list of line plot styles:*)
   Replace[Cases[
     lines, {c__, Line[__], ___} :> 
      Flatten[Directive @@ Cases[{c}, Except[_Line]]], 
     Infinity], {} -> None],
   (*Second return value:marker symbols*)
   Replace[Join[
     Cases[markers, {c__, Inset[s_, pos_, d___], e___} :> If[
        (*markers "s" can be strings or graphics*)

        Head[s] === Graphics,
        (*Append scale factor in case it's needed later;
        default 0.01*)
        {s,
         Last[{.01, d}] /. Scaled[f_] :> First[f]
         },
        If[
         (*For strings,
         add line color if no color specified via text styles:*)

             FreeQ[
          s,
          CMYKColor | RGBColor | GrayLevel | Hue], Style[s, c], s]
        ],
      Infinity
      ],
     (*
     Filter out Pointsize-legends don't need it:*)

     Cases[points, {c___, 
        Point[pt__], ___} :> {Graphics[{c, Point[{0, 0}]}] /. 
         PointSize[_] :> PointSize[1], .01}, Infinity]
     ], {} -> None]}]

autoLegend::usage = 
  "Simplified legending for the plot passed as first argument, with \
legends given as second argument. Use the option Alignment -> \
{horizontal, vertical} to place the legend in the PlotRegion in \
scaled coordinates. For other options, see Options[legendMaker] which \
are used by autoLegend.";
Options[autoLegend] = 
  Join[{Alignment -> {Right, Top}, Background -> White, 
    AspectRatio -> Automatic}, 
   FilterRules[Options[legendMaker], 
    Except[Alignment | Background | AspectRatio]]];
autoLegend[plot_Graphics, labels_, opts : OptionsPattern[]] := 
 Module[{lines, markers, align = OptionValue[Alignment]},
  {lines, markers} = extractStyles[plot];
  Graphics[{
    Inset[plot, {-1, -1},
     {Left, Bottom},
     Scaled[1]
     ],
    Inset[
     legendMaker[labels, PlotStyle -> lines, PlotMarkers -> markers, 
      Sequence @@ 
       FilterRules[{opts}, 
        FilterRules[Options[legendMaker], Except[Alignment]]]],
     align,
     Map[If[NumericQ[#], Center, #] &, align]
     ]
    },
   PlotRange -> {{-1, 1}, {-1, 1}}, 
   AspectRatio -> (OptionValue[AspectRatio] /. 
       Automatic :> (AspectRatio /. Options[plot, AspectRatio]) /. 
      Automatic :> (AspectRatio /. 
         AbsoluteOptions[plot, AspectRatio]))]]


(* ::Section:: *)
(*Approximation Analytics*)


simpleError[\[Theta]_,n_,R_:rR,round_:IntegerPart]:=Module[{nR,pos,out,rep,rules},
Unprotect[round];SetAttributes[round,Listable];Protect[round];
If[TrueQ[Head[R[\[Theta]]]==Piecewise],
pos =Position[R[\[Theta]],List[List[_,_,_],List[_,_,_],List[_,_,_]]];
nR=MapAt[round[2^n #]/(2^n)&,R[\[Theta]],pos]/.{round[2^n]-> 2^n,round[2^(n-1)]-> 2^(n-1)};
out=R[\[Theta]]; rep=Extract[R[\[Theta]],pos]-Extract[nR,pos];
rules=Table[pos[[i]]->rep[[i]],{i,1,Length[pos]}];
ReplacePart[out,rules],(round[2^n R[\[Theta]]]/(2^n)-R[\[Theta]]/.{round[2^n]-> 2^n,round[2^(n-1)]-> 2^(n-1)})]]


fRScaledError[\[Theta]_,m_,round_:IntegerPart]:=Piecewise[{
  {{{1, 1, 1}, 
{-(2^(1 - m)*Cos[\[Theta]]*round[2^(-1 + m)*Sec[\[Theta]]*Sin[Pi/6 + \[Theta]]]), Cos[\[Theta]], 
     -(2^(1 - m)*Cos[\[Theta]]*round[2^(-1 + m)*Sec[\[Theta]]*Sin[Pi/6 - \[Theta]]])},
 {-(2^(1 - m)*round[2^(-1 + m)*Cos[Pi/6 + \[Theta]]*Csc[\[Theta]]]*Sin[\[Theta]]), 
     -(Sin[\[Theta]]), 2^(1 - m)*round[2^(-1 + m)*Cos[Pi/6 - \[Theta]]*Csc[\[Theta]]]*Sin[\[Theta]]}}-rR[\[Theta]], 
   Inequality[Pi/6, LessEqual, Mod[\[Theta], Pi/2], Less, Pi/3]}, 
  {{{1, 1, 1}, {-(2^(1 - m)*round[2^(-1 + m)*Csc[Pi/6 - \[Theta]]*Sin[Pi/6 + \[Theta]]]*Sin[Pi/6 - \[Theta]]), 
     2^(1 - m)*round[2^(-1 + m)*Cos[\[Theta]]*Csc[Pi/6 - \[Theta]]]*Sin[Pi/6 - \[Theta]], -(Sin[Pi/6 - \[Theta]])}, 
    {-(2^(1 - m)*Cos[Pi/6 - \[Theta]]*round[2^(-1 + m)*Cos[Pi/6 + \[Theta]]*Sec[Pi/6 - \[Theta]]]), 
     -(2^(1 - m)*Cos[Pi/6 - \[Theta]]*round[2^(-1 + m)*Sec[Pi/6 - \[Theta]]*Sin[\[Theta]]]), Cos[Pi/6 - \[Theta]]}}-rR[\[Theta]], 
   Inequality[Pi/3, LessEqual, Mod[\[Theta], Pi/2], Less, Pi/2]},
{{{1, 1, 1}, {-(Sin[Pi/6 + \[Theta]]), 
   2^(1 - m)*round[2^(-1 + m)*Cos[\[Theta]]*Csc[Pi/6 + \[Theta]]]*Sin[Pi/6 + \[Theta]], 
   -(2^(1 - m)*round[2^(-1 + m)*Csc[Pi/6 + \[Theta]]*Sin[Pi/6 - \[Theta]]]*Sin[Pi/6 + \[Theta]])}, {-(Cos[Pi/6 + \[Theta]]), 
   -(2^(1 - m)*Cos[Pi/6 + \[Theta]]*round[2^(-1 + m)*Sec[Pi/6 + \[Theta]]*Sin[\[Theta]]]), 
   2^(1 - m)*Cos[Pi/6 + \[Theta]]*round[2^(-1 + m)*Cos[Pi/6 - \[Theta]]*Sec[Pi/6 + \[Theta]]]}}-rR[\[Theta]],Mod[\[Theta], Pi/2] >= 0 || Mod[\[Theta], Pi/2] < Pi/2}},Null]


fRScaledErrorCube=Function[{\[Theta],n,round},Evaluate[ApplyToPiecewise[#.(2^n RGBCube["RGB"])&,fRScaledError[\[Theta],n,round]]]];


rRfRErrorPlot[range_:{0,Pi/6},n_]:= Module[{},
err[\[Theta]_]:=ApplyToPiecewise[#.RGBCube["RGB"]&,fRScaledError[\[Theta],n,IntegerPart]];
errR[\[Theta]_]:=ApplyToPiecewise[#.RGBCube["RGB"]&,fRScaledError[\[Theta],n,Round]];
Grid[{{plot[f,{\[Theta],range[[1]],range[[2]]},Ticks->{PiTicks[range[[1]],range[[2]],12],All},PlotStyle -> Map[RGBColor,Transpose[RGBCube["RGB"]]]]/. {f-> Table[ApplyToPiecewise[#[[2,i]]&,err[\[Theta]]],{i,1,8}],plot->Plot},plot[f,{\[Theta],range[[1]],range[[2]]},Ticks->{PiTicks[range[[1]],range[[2]],12],All},PlotStyle -> Map[RGBColor,Transpose[RGBCube["RGB"]]]]/. {f-> Table[ApplyToPiecewise[#[[2,i]]&,errR[\[Theta]]],{i,1,8}],plot->Plot}},{plot[f,{\[Theta],range[[1]],range[[2]]},Ticks->{PiTicks[range[[1]],range[[2]],12],All},PlotStyle -> Map[RGBColor,Transpose[RGBCube["RGB"]]]]/. {f-> Table[ApplyToPiecewise[#[[3,i]]&,err[\[Theta]]],{i,1,8}],plot->Plot},plot[f,{\[Theta],range[[1]],range[[2]]},Ticks->{PiTicks[range[[1]],range[[2]],12],All},PlotStyle -> Map[RGBColor,Transpose[RGBCube["RGB"]]]]/. {f-> Table[ApplyToPiecewise[#[[3,i]]&,errR[\[Theta]]],{i,1,8}],plot->Plot}}}]]


errorPlotLabel[n_,chan_, round_:IntegerPart]:=Row[{"The error in channel ",chan," with R \[Element] ",("2")^n," using ",round}]


errorPlot[n_,chan_,range_:{0,Pi/2},errFun_:rRErrorCube, round_:IntegerPart,opts:OptionsPattern[]]:= Module[{},
pltFun[fun_,xRange_, ops:OptionsPattern[]]:= Plot[fun,xRange,
PlotRange->{range,All},
FrameTicks->{PiTicks[range[[1]],range[[2]],3(range[[2]]-range[[1]])/(Pi/6)],All},
ExclusionsStyle-> None,Frame -> True,
PlotStyle->Map[RGBColor,Transpose[RGBCube["RGB"]]],PlotLabel->errorPlotLabel[n,chan, round],
FrameLabel->{"\[Theta]","Error"},
ImageSize->400,Evaluate[FilterRules[{ops}, Options[Plot]]]];
plot[f,{\[Theta],range[[1]],range[[2]]},opts]/. {f-> Table[ApplyToPiecewise[#[[chan,i]]&,errFun[\[Theta],n,round]  ],{i,1,8}],plot->pltFun}
]


simpleErrorPlot[range_:{0,Pi/2},errFun_:rRErrorCube,n_,opts:OptionsPattern[]]:= Module[{},
Grid[{{
errorPlot[n,2,{range[[1]],range[[2]]},errFun, IntegerPart,opts],
errorPlot[n,2,{range[[1]],range[[2]]},errFun, Round,opts]},{
errorPlot[n,3,{range[[1]],range[[2]]},errFun, IntegerPart,opts],
errorPlot[n,3,{range[[1]],range[[2]]},errFun, Round,opts]}}]]


(* ::Text:: *)
(*thetaOne[n_] := Block[{fun}, fun[y_] := ArcTan[(Sqrt[3] (1 + y))/Sqrt[1 + y + y^2], (1 - y)/Sqrt[1 + y + y^2]]; Table[fun[i/(2^(n - 1))], {i, 2^(n - 1), 0, -1}]]*)


(* ::Text:: *)
(*thetaTwo[n_] := Block[{funTwo}, funTwo[y_] := ArcTan[(2 + y)/Sqrt[1 + y + y^2], (Sqrt[3] y)/Sqrt[1 + y + y^2]]; Table[funTwo[i/(2^(n - 1))], {i, 0, 2^(n - 1)}]]*)


thetaOne[n_]:=Block[{fun},fun[y_]:=ArcTan[(Sqrt[3] (1+y))/Sqrt[1+y+y^2],(1-y)/Sqrt[1+y+y^2]];Table[fun[i/(2^(n))],{i,2^(n),0,-1}]]
thetaTwo[n_]:=Block[{funTwo},funTwo[y_]:=ArcTan[(2+y)/Sqrt[1+y+y^2],(Sqrt[3] y)/Sqrt[1+y+y^2]];Table[funTwo[i/(2^(n))],{i,0,2^(n)}]]


setupThetaRanges[n_]:=Module[{},
Clear[thetaOneVals,thetaOneMid,thetaOneRange,thetaOneToPoint,thetaTwoVals,thetaTwoMid,thetaTwoRange,thetaTwoToPoint,thetaVals,thetaMid,thetaRange,thetaToPoint];
thetaOneVals=thetaOne[n];
thetaOneMid=(Rest[thetaOneVals]+Most[thetaOneVals])/2;
thetaOneRange=Thread[Inequality[Most[thetaOneVals],Less,Mod[ \[Theta],Pi/6],LessEqual,Rest[thetaOneVals]]];
thetaOneToPoint=Function[{\[Theta]},Evaluate[Piecewise[{{0,\[Theta]==0},Sequence@@Table[{i,thetaOneRange[[i]]},{i,1,Length[thetaOneRange]}]},Length[thetaOneRange]+1]]];
SetAttributes[thetaOneToPoint,Listable];
thetaTwoVals=thetaTwo[n];
thetaTwoMid=(Rest[thetaTwoVals]+Most[thetaTwoVals])/2;
thetaTwoRange=Thread[Inequality[Most[thetaTwoVals],Less,Mod[ \[Theta],Pi/6],LessEqual,Rest[thetaTwoVals]]];
thetaTwoToPoint=Function[{\[Theta]},Evaluate[Piecewise[{{0,\[Theta]==0},Sequence@@Table[{i,thetaTwoRange[[i]]},{i,1,Length[thetaTwoRange]}]},Length[thetaOneRange]+1]]];
SetAttributes[thetaTwoToPoint,Listable];
thetaVals=Sort[Union[thetaOneVals,thetaTwoVals],Less];
thetaMid=(Rest[thetaVals]+Most[thetaVals])/2 ;
thetaRange = Thread[Inequality[Most[thetaVals],Less,Mod[ \[Theta],Pi/6],LessEqual,Rest[thetaVals]]];
thetaToPoint=Function[{\[Theta]},{thetaOneToPoint[\[Theta]],thetaTwoToPoint[\[Theta]]}];
SetAttributes[thetaToPoint,Listable];
]


errorMinTheta[nn_]:=Module[{intersect,index,occurance,extraTheta,order,pts1,pts2,thetaMidPoints,inter,occ,pad},
setupThetaRanges[nn]; 
pts1=ptsOne[nn];pts2=ptsTwo[nn];
thetaMidPoints=Map[thetaToPoint,thetaMid];
inter=Table[intersectionFromPoints[pts1[[All,thetaMidPoints[[i,1]]]],pts2[[All,thetaMidPoints[[i,2]]]]],{i,1,Length[thetaMidPoints]}];
occ=Transpose[{Occurance[Transpose[thetaMidPoints][[1]],Reverse],Occurance[Transpose[thetaMidPoints][[2]]]}];
extraTheta=Intersection[thetaOneVals,thetaTwoVals];
pad=Table[0,{i,1,Length[extraTheta]}];
index=Prepend[thetaMidPoints,sequence@@Map[thetaToPoint,extraTheta]]/.sequence->Sequence;
intersect=Prepend[inter,sequence@@Transpose[{extraTheta,pad }]]/.sequence->Sequence;
occurance=Prepend[occ,sequence@@Transpose[{pad,pad }]]/.sequence->Sequence;
order=Ordering[N[intersect[[All,1]]]];
index=index[[order]]; intersect=intersect[[order]]; occurance =occurance[[order]];
Transpose[{intersect,index,occurance}]
]


classifyByNegPowerOfTwo[{{x_,y_},{indxA_,indxB_},{occA_,occB_}}]:={{x,y},Ceiling[-Log[Abs[y]]/Log[2]]}


classifyByPosition[{{x_,y_},{indxA_,indxB_},{occA_,occB_}}]:={{x,y},occA+occB+1}


convRound[{{x_,y_},{indxA_,indxB_},{occA_,occB_}}]:={{x,If[y< 0.5,y,y-1]},{indxA,indxB},{occA,occB}}


(* ::Section:: *)
(*Representations of the Rotation*)
