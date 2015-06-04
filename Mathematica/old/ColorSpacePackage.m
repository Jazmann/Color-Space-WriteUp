(* ::Package:: *)

Clear[ShowFun]
SetAttributes[ShowFun,HoldAllComplete];
ShowFun[f_[args__]]:=Row[{TraditionalForm[f[Sequence@@Map[ToString,{args}]]]," = ",TraditionalForm[f[args]]}]


(* ::Section:: *)
(*Rotation Matrices*)


Format[\[Theta]1, TraditionalForm] = Subscript[\[Theta], 1];
Format[\[Theta]2, TraditionalForm] = Subscript[\[Theta], 2];
Format[\[Theta]3, TraditionalForm] = Subscript[\[Theta], 3];
Format[\[Theta]4, TraditionalForm] = Subscript[\[Theta], 4];
Format[\[Theta]5, TraditionalForm] = Subscript[\[Theta], 5];
Format[\[Theta]6, TraditionalForm] = Subscript[\[Theta], 6];


ClearAll[RotationMatrixX,RotationMatrixY,RotationMatrixZ,R,\[Alpha]]
RotationMatrixX[\[Alpha]:Except[_String]]:={{1, 0, 0}, {0, Cos[\[Alpha]], Sin[\[Alpha]]}, {0, -Sin[\[Alpha]], Cos[\[Alpha]]}};
Format[RotationMatrixX, TraditionalForm]=Subscript[Style["R",Bold],"X"];
RotationMatrixY[\[Beta]:Except[_String]]:={{Cos[\[Beta]], 0, -Sin[\[Beta]]}, {0, 1, 0}, {Sin[\[Beta]], 0, Cos[\[Beta]]}};
Format[RotationMatrixY, TraditionalForm]=Subscript[Style["R",Bold],"Y"];
RotationMatrixZ[\[Gamma]:Except[_String]]:={{Cos[\[Gamma]], Sin[\[Gamma]], 0}, {-Sin[\[Gamma]], Cos[\[Gamma]], 0}, {0, 0, 1}};
Format[RotationMatrixZ, TraditionalForm]=Subscript[Style["R",Bold],"Z"];
RotationMatrixXYZ[\[Alpha]:Except[_String],\[Beta]:Except[_String],\[Gamma]:Except[_String]]:=Evaluate[TrigReduce[RotationMatrixX[\[Alpha]].RotationMatrixZ[\[Gamma]].RotationMatrixY[\[Beta]]]];
Format[RotationMatrixXYZ, TraditionalForm]=Subscript[Style["R",Bold],"XYZ"];


Row[{ShowFun[RotationMatrixX[\[Alpha]]],"    ",ShowFun[RotationMatrixY[\[Beta]]],"    ",ShowFun[RotationMatrixZ[\[Gamma]]]}]
ShowFun[RotationMatrixXYZ[\[Alpha],\[Beta],\[Gamma]]]


(* ::Subsection::Closed:: *)
(*R*)


LCaCb[\[Theta]:Except[_String]]:= Evaluate[TrigFactor[RotationMatrixX[\[Theta]].RotationMatrixZ[ArcTan[1/Sqrt[2]]].RotationMatrixY[-Pi/4]]];
Format[LCaCb, TraditionalForm]=Style["R",Bold];
iLCaCb[\[Theta]:Except[_String]]:= Evaluate[TrigFactor[RotationMatrixY[Pi/4].RotationMatrixZ[-ArcTan[1/Sqrt[2]]].RotationMatrixX[-\[Theta]]]];
Format[iLCaCb, TraditionalForm]=Superscript[Style["R",Bold],"-1"];


ShowFun[LCaCb[\[Theta]]]
ShowFun[iLCaCb[\[Theta]]]


(* ::Subsection::Closed:: *)
(*nR*)


(* ::Subsubsection:: *)
(*Matrix*)


Format[\[Theta]2m1, TraditionalForm] = Subsuperscript[Style["\[Theta]",Bold],2,-1];
Format[\[Theta]2,   TraditionalForm] = Subscript[Style["\[Theta]",Bold],2];


nLCaCb[\[Theta]:Except[_String]]:={{1/3, 1/3, 1/3}, {-(Sec[Pi/6 - Mod[-Pi/6 + \[Theta], Pi/3]]*Sin[Pi/6 + \[Theta]])/2, 
  (Cos[\[Theta]]*Sec[Pi/6 - Mod[-Pi/6 + \[Theta], Pi/3]])/2, 
  -(Sec[Pi/6 - Mod[-Pi/6 + \[Theta], Pi/3]]*Sin[Pi/6 - \[Theta]])/2}, 
 {-(Cos[Pi/6 + \[Theta]]*Sec[Pi/6 - Mod[\[Theta], Pi/3]])/2, -(Sec[Pi/6 - Mod[\[Theta], Pi/3]]*Sin[\[Theta]])/
   2, (Cos[Pi/6 - \[Theta]]*Sec[Pi/6 - Mod[\[Theta], Pi/3]])/2}}


Clear[nLCaCbFun,nLCaCb]
nLCaCbFun=Function[{\[Theta], \[Theta]2m1, \[Theta]2},{
{1/3, 1/3, 1/3}, 
{-(Sec[Pi/6 - \[Theta]2m1]*Sin[Pi/6 + \[Theta] ])/2, (Cos[\[Theta]]*Sec[Pi/6 - \[Theta]2m1])/2, -(Sec[Pi/6 - \[Theta]2m1]*Sin[Pi/6 - \[Theta] ])/2}, 
{-(Cos[Pi/6 + \[Theta]   ]*Sec[Pi/6 - \[Theta]2])/2,  -(Sec[Pi/6 - \[Theta]2]*Sin[\[Theta]])/2,  (Cos[Pi/6 - \[Theta]   ]*Sec[Pi/6 - \[Theta]2])/2}}];

nLCaCb[\[Theta]:Except[_String], \[Theta]2m1_, \[Theta]2_]:=nLCaCbFun[\[Theta], \[Theta]2m1,\[Theta]2];
nLCaCb[\[Theta]:Except[_String]]:=nLCaCbFun[\[Theta], Mod[\[Theta] - Pi/6, Pi/3], Mod[\[Theta], Pi/3]];
Format[nLCaCb, TraditionalForm]=Style["nR",Bold];


ShowFun[nLCaCb[\[Theta]]]


inLCaCbFun=Function[{\[Theta],\[Theta]2m1,\[Theta]2},{
{1,-(4/3) Cos[\[Pi]/6-\[Theta]2m1] Sin[\[Pi]/6+\[Theta]], -(4/3) Cos[\[Pi]/6+\[Theta]] Cos[\[Pi]/6-\[Theta]2]},
{1, 4/3 Cos[\[Theta]] Cos[\[Pi]/6-\[Theta]2m1],    -(4/3) Cos[\[Pi]/6-\[Theta]2] Sin[\[Theta]]},
{1,-(4/3) Cos[\[Pi]/6-\[Theta]2m1] Sin[\[Pi]/6-\[Theta]],  4/3 Cos[\[Pi]/6-\[Theta]] Cos[\[Pi]/6-\[Theta]2]}}];

inLCaCb[\[Theta]:Except[_String], \[Theta]2m1_, \[Theta]2_]:=inLCaCbFun[\[Theta], \[Theta]2m1,\[Theta]2];
inLCaCb[\[Theta]:Except[_String]]:=inLCaCbFun[\[Theta], Mod[\[Theta] - Pi/6, Pi/3], Mod[\[Theta], Pi/3]];
Format[inLCaCb, TraditionalForm]=Superscript[Style["nLCaCb",Bold],"-1"];



TraditionalForm[Row[{inLCaCb["\[Theta]"]," = ",inLCaCb[\[Theta], \[Theta]2m1, \[Theta]2],"      where     ",
Column[{Row[{\[Theta]2m1," = ",Mod[\[Theta] - Pi/6, Pi/3]}],Row[{\[Theta]2," = ",Mod[\[Theta], Pi/3]}]}]}]]
ShowFun[inLCaCb[\[Theta]]]


(* ::Subsubsection::Closed:: *)
(*Scale*)


scaleFun["nLCaCb","LCaCb"]=Function[{\[Theta],\[Theta]2m1,\[Theta]2}, {1/Sqrt[3],1/2 Sqrt[3/2] Sec[\[Pi]/6 - \[Theta]2m1],1/2 Sqrt[3/2] Sec[\[Pi]/6 - \[Theta]2]}];
scale["nLCaCb","LCaCb"][\[Theta]:Except[_String], \[Theta]2m1_, \[Theta]2_]:=scaleFun["nLCaCb","LCaCb"][\[Theta], \[Theta]2m1,\[Theta]2];
scale["nLCaCb","LCaCb"][\[Theta]:Except[_String]] := scaleFun["nLCaCb","LCaCb"][\[Theta], Mod[\[Theta] - Pi/6, Pi/3], Mod[\[Theta], Pi/3]];
Format[scale["nLCaCb","LCaCb"], TraditionalForm]= Superscript[Style["L",Bold],"-1"];

scaleFun["LCaCb","nLCaCb"]=Function[{\[Theta],\[Theta]2m1,\[Theta]2}, {Sqrt[3],2 Sqrt[2/3] Cos[\[Pi]/6 - \[Theta]2m1],2 Sqrt[2/3] Cos[\[Pi]/6 - \[Theta]2]}];
scale["LCaCb","nLCaCb"][\[Theta]:Except[_String], \[Theta]2m1_, \[Theta]2_]:=scaleFun["LCaCb","nLCaCb"][\[Theta], \[Theta]2m1,\[Theta]2];
scale["LCaCb","nLCaCb"][\[Theta]:Except[_String]] := scaleFun["LCaCb","nLCaCb"][\[Theta], Mod[\[Theta] - Pi/6, Pi/3], Mod[\[Theta], Pi/3]];
Format[scale["LCaCb","nLCaCb"], TraditionalForm]= Style["L",Bold];


TraditionalForm[Row[{scale["LCaCb","nLCaCb"]["\[Theta]"]," = ",MatrixForm@scale["LCaCb","nLCaCb"][\[Theta], \[Theta]2m1, \[Theta]2],"           ",
scale["nLCaCb","LCaCb"]["\[Theta]"]," = ",MatrixForm@scale["nLCaCb","LCaCb"][\[Theta], \[Theta]2m1, \[Theta]2],"      where     ",
Column[{Row[{\[Theta]2m1," = ",Mod[\[Theta] - Pi/6, Pi/3]}],Row[{\[Theta]2," = ",Mod[\[Theta], Pi/3]}]}]}]]
TraditionalForm[Row[{scale["LCaCb","nLCaCb"]["\[Theta]"]," = ",MatrixForm@scale["LCaCb","nLCaCb"][\[Theta]],"           ",
scale["nLCaCb","LCaCb"]["\[Theta]"]," = ",MatrixForm@scale["nLCaCb","LCaCb"][\[Theta]]}]]


Style[TraditionalForm[Row[{nLCaCb["\[Theta]"]," = ",scale["nLCaCb","LCaCb"]["\[Theta]"]," \[CircleTimes] ",LCaCb["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{LCaCb["\[Theta]"]," = ",scale["LCaCb","nLCaCb"]["\[Theta]"]," \[CircleTimes] ",nLCaCb["\[Theta]"]}]],Larger]


(* ::Subsection::Closed:: *)
(*rR*)


(* ::Subsubsection:: *)
(*Matrix*)


Clear[rR];
rR[\[Theta]:Except[_String]]:= ({
 {1, 1, 1},
 {- Sin[\[Theta]+\[Pi]/6],  Cos[\[Theta]],  Sin[\[Theta]-\[Pi]/6]},
 {- Cos[\[Theta]+\[Pi]/6], - Sin[\[Theta]],  Cos[\[Theta]-\[Pi]/6]}
});
Format[rR, TraditionalForm]=TraditionalForm["r\!\(\*StyleBox[\"R\",\nFontWeight->\"Bold\"]\)"];


ShowFun[rR[\[Theta]]]


Clear[irR];
irR[\[Theta]:Except[_String]]:={
{1/3, (-(2/3))*Sin[Pi/6 + \[Theta]], (-(2/3))*Cos[Pi/6 + \[Theta]]}, 
{1/3,           (2*Cos[\[Theta]])/3, -((2*Sin[\[Theta]])/3)}, 
{1/3, (-(2/3))*Sin[Pi/6 - \[Theta]], (2/3)*Cos[Pi/6 - \[Theta]]}};
Format[irR, TraditionalForm]=TraditionalForm["ir\!\(\*StyleBox[\"R\",\nFontWeight->\"Bold\"]\)"];


ShowFun[irR[\[Theta]]]


(* ::Subsubsection:: *)
(*Scale*)


scale["LCaCb","rR"][\[Theta]:Except[_String]] = {1/Sqrt[3],Sqrt[2/3],Sqrt[2/3]};
Format[scale["LCaCb","rR"], TraditionalForm][_String] = Style["rS",Bold];


Style[TraditionalForm[Row[{LCaCb["\[Theta]"]," = ",scale["LCaCb","rR"]["\[Theta]"]," \[CircleTimes] ",rR["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{LCaCb["\[Theta]"]," = ",MatrixForm[scale["LCaCb","rR"][\[Theta]]]," \[CircleTimes] ",rR[\[Theta]]}]],Larger]


(* ::Subsection::Closed:: *)
(*fR*)


(* ::Subsubsection:: *)
(*Matrix*)


Clear[fReEqn,fRe,fREqnForm,fR]
fReEqn=Function[{\[Theta]1},-1/2 (1+Sqrt[3] Tan[\[Theta]1])];
fRe[\[Theta]1:Except[_String]]=fReEqn[\[Theta]1];
Format[fRe, TraditionalForm]=Style["fRe",Bold];

fREqnForm=Function[{\[Theta]6,\[Theta]1,fReqq},Piecewise[{
{{{1,1,1},{fReqq[\[Theta]1],1,-1-fReqq[\[Theta]1]},{fReqq[\[Pi]/6-\[Theta]1],-1-fReqq[\[Pi]/6-\[Theta]1],1}},0<=\[Theta]6<\[Pi]/6},
{{{1,1,1},{1,fReqq[\[Pi]/6-\[Theta]1],-1-fReqq[\[Pi]/6-\[Theta]1]},{-1-fReqq[\[Theta]1],fReqq[\[Theta]1],1}},\[Pi]/6<=\[Theta]6<\[Pi]/3},
{{{1,1,1},{1,-1-fReqq[\[Theta]1],fReqq[\[Theta]1]},{-1-fReqq[\[Pi]/6-\[Theta]1],1,fReqq[\[Pi]/6-\[Theta]1]}},\[Pi]/3<=\[Theta]6<\[Pi]/2},
{{{1,1,1},{fReqq[\[Pi]/6-\[Theta]1],-1-fReqq[\[Pi]/6-\[Theta]1],1},{fReqq[\[Theta]1],1,-1-fReqq[\[Theta]1]}},\[Pi]/2<=\[Theta]6<(2 \[Pi])/3},
{{{1,1,1},{-1-fReqq[\[Theta]1],fReqq[\[Theta]1],1},{1,fReqq[\[Pi]/6-\[Theta]1],-1-fReqq[\[Pi]/6-\[Theta]1]}},(2 \[Pi])/3<=\[Theta]6<(5 \[Pi])/6},
{{{1,1,1},{-1-fReqq[\[Pi]/6-\[Theta]1],1,fReqq[\[Pi]/6-\[Theta]1]},{1,-1-fReqq[\[Theta]1],fReqq[\[Theta]1]}},(5 \[Pi])/6<=\[Theta]6<\[Pi]}},0]];

fR[\[Theta]6:Except[_String],\[Theta]1_,fReqq_]:=fREqnForm[\[Theta]6,\[Theta]1,fReqq];
fR[\[Theta]:Except[_String],fReqq_]:=fREqnForm[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fReqq];
fR[\[Theta]:Except[_String]]:=fREqnForm[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe];

Format[fR, TraditionalForm]=Style["fR",Bold];


TraditionalForm[ShowFun[fR[\[Theta]]]]


TraditionalForm[Row[{ShowFun[fR[\[Theta]6,\[Theta]1,"fRe"]],"      where     ",
Column[{Row[{\[Theta]6," = ",Mod[\[Theta], Pi]}],Row[{\[Theta]1," = ",Mod[\[Theta], Pi/6]}]}]}]]


(* ::Subsubsection:: *)
(*Matrix Decomposition*)


Clear[fRmFun,fROFun]
fRmFun=Function[{\[Theta]1,f},{{1,1,1},{f[\[Theta]1],1,-1-f[\[Theta]1]},{f[\[Pi]/6-\[Theta]1],-1-f[\[Pi]/6-\[Theta]1],1}}];
fROFun=Function[{m,\[Theta]6},Piecewise[{
{{{m[[1,1]],m[[1,2]],m[[1,3]]},{m[[2,1]],m[[2,2]],m[[2,3]]},{m[[3,1]],m[[3,2]],m[[3,3]]}},0<=\[Theta]6<\[Pi]/6},
{{{m[[1,1]],m[[1,2]],m[[1,3]]},{m[[3,3]],m[[3,1]],m[[3,2]]},{m[[2,3]],m[[2,1]],m[[2,2]]}},\[Pi]/6<=\[Theta]6<\[Pi]/3},
{{{m[[1,1]],m[[1,2]],m[[1,3]]},{m[[2,2]],m[[2,3]],m[[2,1]]},{m[[3,2]],m[[3,3]],m[[3,1]]}},\[Pi]/3<=\[Theta]6<\[Pi]/2},
{{{m[[1,1]],m[[1,2]],m[[1,3]]},{m[[3,1]],m[[3,2]],m[[3,3]]},{m[[2,1]],m[[2,2]],m[[2,3]]}},\[Pi]/2<=\[Theta]6<(2 \[Pi])/3},
{{{m[[1,1]],m[[1,2]],m[[1,3]]},{m[[2,3]],m[[2,1]],m[[2,2]]},{m[[3,3]],m[[3,1]],m[[3,2]]}},(2 \[Pi])/3<=\[Theta]6<(5 \[Pi])/6},
{{{m[[1,1]],m[[1,2]],m[[1,3]]},{m[[3,2]],m[[3,3]],m[[3,1]]},{m[[2,2]],m[[2,3]],m[[2,1]]}},(5 \[Pi])/6<=\[Theta]6 <\[Pi]}},0]];
Clear[fRO,fRm]
fRO[m:{{_,_,_},{_,_,_},{_,_,_}},\[Theta]:Except[_String]]:=fROFun[m,Mod[\[Theta],\[Pi]]];
fRm[\[Theta]1:Except[_String],f_:fRe]:=fRmFun[\[Theta]1,f]
Format[fRO, TraditionalForm]=Style["fRO",Bold];
\!\(\*
TagBox[
FormBox[
FormBox[
RowBox[{"Format", "[", 
RowBox[{"fRm", ",", " ", "TraditionalForm"}], "]"}],
TraditionalForm],
TraditionalForm],
Format[#, TraditionalForm]& ]\)=Style["fRm",Bold];


Style[TraditionalForm[Row[{fR["\[Theta]"]," = ",fRO[fRm["\[Theta]"],"\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{fR["\[Theta]"]," = ",fRO[MatrixForm[fRm[\[Theta]1,"fRe"]],\[Theta]6],"      where     ",
Column[{Row[{ "fRe = ",fRe[\[Theta]]}],Row[{TraditionalForm[\[Theta]1]," = ",TraditionalForm[Mod[\[Theta],\[Pi]/6]]}],Row[{TraditionalForm[\[Theta]6]," = ",TraditionalForm[Mod[\[Theta],\[Pi]]]}]}]}]],Larger]
Style[TraditionalForm[Row[{fRO[MatrixForm[{{a1,a2,a3},{b1,b2,b3},{c1,c2,c3}}],\[Theta]]," = ",ApplyToPiecewise[TraditionalForm,fRO[{{a1,a2,a3},{b1,b2,b3},{c1,c2,c3}},\[Theta]]]}]],Larger]


ShowFun[fR[\[Theta]6,\[Theta]1,"fRe"]]


(* ::Subsubsection:: *)
(*Scale*)


scale["rR","fR"][\[Theta]:Except[_String]]:= Piecewise[{
{{1,  Cos[\[Theta]],        Cos[Pi/6 - \[Theta]]},  Inequality[0,        LessEqual, Mod[\[Theta], Pi], Less, Pi/6]}, 
{{1, -Sin[Pi/6 + \[Theta]], Cos[Pi/6 - \[Theta]]},  Inequality[Pi/6,     LessEqual, Mod[\[Theta], Pi], Less, Pi/3]}, 
{{1, -Sin[Pi/6 + \[Theta]], -Sin[\[Theta]]},        Inequality[Pi/3,     LessEqual, Mod[\[Theta], Pi], Less, Pi/2]}, 
{{1, -Sin[Pi/6 - \[Theta]], -Sin[\[Theta]]},        Inequality[Pi/2,     LessEqual, Mod[\[Theta], Pi], Less, (2*Pi)/3]},
{{1, -Sin[Pi/6 - \[Theta]], -Cos[Pi/6 + \[Theta]]}, Inequality[(2*Pi)/3, LessEqual, Mod[\[Theta], Pi], Less, (5*Pi)/6]}, 
{{1,  Cos[\[Theta]],        -Cos[Pi/6 + \[Theta]]}, Inequality[(5*Pi)/6, LessEqual, Mod[\[Theta], Pi], Less, Pi]}}
, 0]
Format[scale["rR","fR"], TraditionalForm]=Style["fS",Bold];


(* ::Subsubsection:: *)
(*Scale Decomposition*)


Clear[fSse,fSs]; 
fSse[\[Theta]:Except[_String]] = {1, Cos[Mod[\[Theta] - Pi/6, Pi/3] - Pi/6], Cos[Mod[\[Theta], Pi/3] - Pi/6]}; 
fSsFun = Function[{\[Theta]6},Piecewise[{{
       {1,  1,  1}, Inequality[0,        LessEqual, \[Theta]6, Less, Pi/6]}, 
      {{1, -1,  1}, Inequality[Pi/6,     LessEqual, \[Theta]6, Less, Pi/3]},
      {{1, -1, -1}, Inequality[Pi/3,     LessEqual, \[Theta]6, Less, Pi/2]},
      {{1,  1, -1}, Inequality[Pi/2,     LessEqual, \[Theta]6, Less, (2*Pi)/3]}, 
      {{1,  1,  1}, Inequality[(2*Pi)/3, LessEqual, \[Theta]6, Less, (5*Pi)/6]}, 
      {{1, -1,  1}, Inequality[(5*Pi)/6, LessEqual, \[Theta]6, Less, Pi]}}, 0]];
fSs[\[Theta]:Except[_String]] = fSsFun[Mod[\[Theta], Pi]];
Format[fSse, TraditionalForm]=Style["fSse",Bold];
Format[fSs,  TraditionalForm]=Style["fSs", Bold];


Style[TraditionalForm[Row[{scale["rR","fR"]["\[Theta]"]," = ",fSse["\[Theta]"]," \[CircleTimes] ",fSs["\!\(\*SubscriptBox[\(\[Theta]\), \(6\)]\)"]}]],Larger]
Style[TraditionalForm[Row[{fSs["\!\(\*SubscriptBox[\(\[Theta]\), \(6\)]\)"]," = ",MatrixForm[fSse[\[Theta]6]]," \[CircleTimes] ",fSsFun[\[Theta]4]}]],Larger]


Clear[fSoo,fSo];
fSooFun = Function[{\[Theta]4},Piecewise[{
      {{1,  1,  1}, Inequality[0,    LessEqual, \[Theta]4, Less, Pi/6]}, 
      {{1, -1,  1}, Inequality[Pi/6, LessEqual, \[Theta]4, Less, Pi/3]}, 
      {{1, -1, -1}, Inequality[Pi/3, LessEqual, \[Theta]4, Less, Pi/2]}, 
      {{1,  1, -1}, Inequality[Pi/2, LessEqual, \[Theta]4, Less, (2*Pi)/3]}}, 0]]; 
fSoo[\[Theta]:Except[_String]] := fSooFun[Mod[\[Theta], 2*(Pi/3)]];
fSoFun[\[Theta]6:Except[_String]] = Piecewise[{
      {{1,  1,  1}, Inequality[0,  LessEqual, \[Theta]6, Less,   Pi]}, 
      {{1, -1, -1}, Inequality[Pi, LessEqual, \[Theta]6, Less, 2*Pi]}}, 0]; 
fSo[\[Theta]:Except[_String]] := fSoFun[Mod[\[Theta], 2*Pi]];
Format[fSoo, TraditionalForm]=Style["fSoo",Bold];
Format[fSo,  TraditionalForm]=Style["fSo", Bold];



Style[TraditionalForm[Row[{scale["rR","fR"]["\[Theta]"]," = ",fSse["\[Theta]"]," \[CircleTimes] ",fSs["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{fSs["\!\(\*SubscriptBox[\(\[Theta]\), \(6\)]\)"]," = ",fSo["\[Theta]"]," \[CircleTimes] ",fSoo["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{fSs["\!\(\*SubscriptBox[\(\[Theta]\), \(6\)]\)"]," = ",fSoFun[\[Theta]6]," \[CircleTimes] ",fSooFun[\[Theta]4]}]],Larger]


(* ::Subsubsection:: *)
(*Relationships*)


Style[TraditionalForm[Row[{LCaCb["\[Theta]"]," = ",scale["LCaCb","rR"]["\[Theta]"]," \[CircleTimes] ",scale["rR","fR"]["\[Theta]"]," \[CircleTimes] ",fR["\!\(\*SubscriptBox[\(\[Theta]\), \(6\)]\)",\[Theta]1,"fRe"]}]],Larger]


Style[TraditionalForm[Row[{LCaCb["\[Theta]"]," = ",MatrixForm[scale["LCaCb","rR"][\[Theta]]]," \[CircleTimes] ",MatrixForm[scale["rR","fR"][\[Theta]]]," \[CircleTimes] ",fR[\[Theta]6,\[Theta]1,"fRe"]}]],Larger]


(* ::Subsection::Closed:: *)
(*fRs*)


(* ::Subsubsection:: *)
(*Matrix*)


fRsFun=Function[{\[Theta]6,\[Theta]1,fReqq},Piecewise[{{{{1, 1, 1}, {-1, -fReqq[Pi/6 - \[Theta]1], 1 + fReqq[Pi/6 - \[Theta]1]}, 
    {-1 - fReqq[\[Theta]1], fReqq[\[Theta]1], 1}}, Inequality[Pi/6, LessEqual, \[Theta]6, Less, Pi/3]}, 
  {{{1, 1, 1}, {-1, 1 + fReqq[\[Theta]1], -fReqq[\[Theta]1]}, {1 + fReqq[Pi/6 - \[Theta]1], -1, 
     -fReqq[Pi/6 - \[Theta]1]}}, Inequality[Pi/3, LessEqual, \[Theta]6, Less, Pi/2]}, 
  {{{1, 1, 1}, {fReqq[Pi/6 - \[Theta]1], -1 - fReqq[Pi/6 - \[Theta]1], 1}, 
    {-fReqq[\[Theta]1], -1, 1 + fReqq[\[Theta]1]}}, Inequality[Pi/2, LessEqual, \[Theta]6, Less, 
    (2*Pi)/3]}, {{{1, 1, 1}, {1 + fReqq[Pi/6 - \[Theta]1], -1, -fReqq[Pi/6 - \[Theta]1]}, 
    {1, -1 - fReqq[\[Theta]1], fReqq[\[Theta]1]}}, Inequality[(5*Pi)/6, LessEqual, \[Theta]6, Less, Pi]}, 
  {{{1, 1, 1}, {-1 - fReqq[\[Theta]1], fReqq[\[Theta]1], 1}, {1, fReqq[Pi/6 - \[Theta]1], 
     -1 - fReqq[Pi/6 - \[Theta]1]}}, Inequality[(2*Pi)/3, LessEqual, \[Theta]6, Less, (5*Pi)/6]}, 
  {{{1, 1, 1}, {fReqq[\[Theta]1], 1, -1 - fReqq[\[Theta]1]}, {fReqq[Pi/6 - \[Theta]1], 
     -1 - fReqq[Pi/6 - \[Theta]1], 1}}, Inequality[0, LessEqual, \[Theta]6, Less, Pi/6]}}, 0]];
Clear[fRs]
fRs[\[Theta]6:Except[_String],\[Theta]1_,fReqq_]:=fRsFun[\[Theta]6,\[Theta]1,fReqq];
fRs[\[Theta]:Except[_String],fReqq_]:=fRsFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fReqq];
fRs[\[Theta]:Except[_String]]:=fRsFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe];

Format[fRs, TraditionalForm]=Style["fRs",Bold];


(* ::Subsubsection:: *)
(*Scale*)


scale["rR","fRs"][\[Theta]:Except[_String]]:= {1, Cos[Mod[\[Theta] - Pi/6, Pi/3] - Pi/6], Cos[Mod[\[Theta], Pi/3] - Pi/6]}; 
Format[scale["rR","fRs"], TraditionalForm]=Style["fSse",Bold];


Style[TraditionalForm[Row[{LCaCb["\[Theta]"]," = ",scale["LCaCb","rR"]["\[Theta]"]," \[CircleTimes] ",scale["rR","fRs"]["\[Theta]"]," \[CircleTimes] ",fRs["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{nLCaCb["\[Theta]"]," = ",scale["nLCaCb","LCaCb"]["\[Theta]"]," \[CircleTimes] ",scale["LCaCb","rR"]["\[Theta]"]," \[CircleTimes] ",scale["rR","fRs"]["\[Theta]"]," \[CircleTimes] ",fRs["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{fRs["\[Theta]"]," = ",fSs["\[Theta]"]," \[CircleTimes] ",fR["\[Theta]"]}]],Larger]


(* ::Subsection::Closed:: *)
(*qR*)


(* ::Subsubsection:: *)
(*Matrix*)


Clear[qReFun,qRe,qRmFun,qRm,qR]
qReFun=Function[{\[Theta],n},-2^(n-3) (1+Sqrt[3] Tan[\[Theta]])];
qRe[\[Theta]1:Except[_String]]:=qReFun[\[Theta]1];
Format[qRe, TraditionalForm]=Style["qRe",FontWeight->"Bold"];

qRmFun = Function[{\[Theta]1, f, n}, {{1, 1, 1}, {Round[2^(-2 + n)*f[\[Theta]1]], 2^(-2 + n), -2^(-2 + n) - Round[2^(-2 + n)*f[\[Theta]1]]}, 
     {Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], -2^(-2 + n) - Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], 2^(-2 + n)}}];
qRm[\[Theta]1:Except[_String],f_:fRe]:=fRmFun[\[Theta]1,f];
\!\(\*
TagBox[
FormBox[
FormBox[
RowBox[{"Format", "[", 
RowBox[{"qRm", ",", " ", "TraditionalForm"}], "]"}],
TraditionalForm],
TraditionalForm],
Format[#, TraditionalForm]& ]\)="qRm";
qRFun = Function[{\[Theta]6, \[Theta]1, f, n}, Piecewise[{{{{1, 1, 1}, {Round[2^(-2 + n)*f[\[Theta]1]], 2^(-2 + n), -2^(-2 + n) - Round[2^(-2 + n)*f[\[Theta]1]]}, 
        {Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], -2^(-2 + n) - Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], 2^(-2 + n)}}, 
       Inequality[0, LessEqual, \[Theta]6, Less, Pi/6]}, {{{1, 1, 1}, {2^(-2 + n), Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], 
         -2^(-2 + n) - Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]]}, {-2^(-2 + n) - Round[2^(-2 + n)*f[\[Theta]1]], Round[2^(-2 + n)*f[\[Theta]1]], 2^(-2 + n)}}, 
       Inequality[Pi/6, LessEqual, \[Theta]6, Less, Pi/3]}, {{{1, 1, 1}, {2^(-2 + n), -2^(-2 + n) - Round[2^(-2 + n)*f[\[Theta]1]], 
         Round[2^(-2 + n)*f[\[Theta]1]]}, {-2^(-2 + n) - Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], 2^(-2 + n), Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]]}}, 
       Inequality[Pi/3, LessEqual, \[Theta]6, Less, Pi/2]}, {{{1, 1, 1}, {Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], 
         -2^(-2 + n) - Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], 2^(-2 + n)}, {Round[2^(-2 + n)*f[\[Theta]1]], 2^(-2 + n), 
         -2^(-2 + n) - Round[2^(-2 + n)*f[\[Theta]1]]}}, Inequality[Pi/2, LessEqual, \[Theta]6, Less, (2*Pi)/3]}, 
      {{{1, 1, 1}, {-2^(-2 + n) - Round[2^(-2 + n)*f[\[Theta]1]], Round[2^(-2 + n)*f[\[Theta]1]], 2^(-2 + n)}, 
        {2^(-2 + n), Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], -2^(-2 + n) - Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]]}}, 
       Inequality[(2*Pi)/3, LessEqual, \[Theta]6, Less, (5*Pi)/6]}, {{{1, 1, 1}, {-2^(-2 + n) - Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]], 2^(-2 + n), 
         Round[2^(-2 + n)*f[Pi/6 - \[Theta]1]]}, {2^(-2 + n), -2^(-2 + n) - Round[2^(-2 + n)*f[\[Theta]1]], Round[2^(-2 + n)*f[\[Theta]1]]}}, 
       Inequality[(5*Pi)/6, LessEqual, \[Theta]6, Less, Pi]}}, 0]];
qR[\[Theta]6:Except[_String],\[Theta]1_,fReqq_,n_]:=qRFun[\[Theta]6,\[Theta]1,fReqq,n];
qR[\[Theta]:Except[_String],fReqq_,n_]:=qRFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fReqq,n];
qR[\[Theta]:Except[_String],n_]:=qRFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe,n];
qR[\[Theta]:Except[_String]]:=qRFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe,8];

Format[qR, TraditionalForm]=Style["qR",FontWeight->"Bold"];


ShowFun[qR[\[Theta]6,\[Theta]1,"fRe",n]]








(* ::Subsubsection:: *)
(*Scale*)


scale["qR","fR"][\[Theta]:Except[_String],n_:8]:={1,2^(n-2),2^(n-2)};
Format[scale["qR","fR"], TraditionalForm]= Superscript[Style["qS",Bold],"-1"];
scale["fR","qR"][\[Theta]:Except[_String],n_:8]:={1,2^(2-n),2^(2-n)};
Format[scale["fR","qR"], TraditionalForm]=Style["qS",Bold];


Style[TraditionalForm[Row[{fR["\[Theta]"]," = ",scale["fR","qR"]," \[CircleTimes] ",qR["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{nLCaCb["\[Theta]"]," = ",scale["nLCaCb","LCaCb"]["\[Theta]"]," \[CircleTimes] ",scale["LCaCb","rR"]["\[Theta]"]," \[CircleTimes] ",scale["rR","fRs"]["\[Theta]"]," \[CircleTimes] ",fSs["\[Theta]"]," \[CircleTimes] ",scale["fR","qR"]," \[CircleTimes] ",qR["\[Theta]"]}]],Larger]


(* ::Subsection::Closed:: *)
(*dqR*)


(* ::Subsubsection:: *)
(*Matrix*)


Clear[\[Delta]qRe,\[Delta]qReFun,\[Delta]qRm,\[Delta]qRmFun,\[Delta]qR]
\[Delta]qReFun=Function[{\[Theta]1,f,n},Assuming[Element[n,Integers]&&n>3,Simplify[2^(-2+n) f[\[Theta]1]-Distribute[Round[(Expand[2^(-2+n) f[\[Theta]1]])],Plus]/.
{Round[Times[-1,expr_]]:> Times[-1,Round[expr]],Round[Plus[expr__]]:> Distribute[Round[Plus[expr]],Plus,Round]}]]];
\[Delta]qRe[\[Theta]1:Except[_String],fRe_,n_]:=Assuming[Element[n,Integers]&&n>3,Simplify[\[Delta]qReFun[\[Theta]1,fRe,n]]];
\[Delta]qRe[\[Theta]1:Except[_String],n_]:=Assuming[Element[n,Integers]&&n>3,Simplify[\[Delta]qReFun[\[Theta]1,fRe,n]]];
\[Delta]qRe[\[Theta]1:Except[_String]]:=Assuming[Element[n,Integers]&&n>3,Simplify[\[Delta]qReFun[\[Theta]1,fRe,8]]];
Format[\[Delta]qRe, TraditionalForm]=Style["\[Delta]qRe",Bold];
\[Delta]qRmFun=Function[{\[Theta]1,\[Delta]qRe,fRe,n},{{0,0,0},
{\[Delta]qRe[   \[Theta]1,fRe,n],0, - \[Delta]qRe[\[Theta]1,fRe,n]},
{\[Delta]qRe[\[Pi]/6-\[Theta]1,fRe,n], - \[Delta]qRe[\[Pi]/6-\[Theta]1,fRe,n],0}}];
(* \[Delta]qRmFun=Function[{\[Theta]1,f,n},Evaluate[Assuming[Element[n,Integers]&&n>3,Simplify[Expand[scale["qR","fR"][\[Theta],n] fRm[\[Theta]1,f] - qRmFun[\[Theta]1,f,n]]] ]]]; *)
\[Delta]qRm[\[Theta]1:Except[_String],\[Delta]qRe_,fRe_,n_]:=\[Delta]qRmFun[\[Theta]1,\[Delta]qRe,fRe,n];
\[Delta]qRm[\[Theta]1:Except[_String],\[Delta]qRe_,n_]:=\[Delta]qRmFun[\[Theta]1,\[Delta]qRe,n];
\[Delta]qRm[\[Theta]1:Except[_String],n_]:=\[Delta]qRmFun[\[Theta]1,\[Delta]qRe,fRe,n];
\[Delta]qRm[\[Theta]1:Except[_String]]:=\[Delta]qRmFun[\[Theta]1,\[Delta]qRe,fRe,8];
Format[\[Delta]qRm, TraditionalForm]=Style["\[Delta]qRm",Bold];
\[Delta]qRFun=Function[{\[Theta]6,\[Theta]1,fReq,n},Evaluate[fROFun[\[Delta]qRmFun[\[Theta]1,\[Delta]qRe,fReq,n],\[Theta]6]]];

\[Delta]qR[\[Theta]6:Except[_String],\[Theta]1_,fRe_,n_]:=\[Delta]qRFun[\[Theta]6,\[Theta]1,fRe,n];
\[Delta]qR[\[Theta]:Except[_String],fRe_,n_]:=\[Delta]qRFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe,n];
\[Delta]qR[\[Theta]:Except[_String],n_]:=\[Delta]qRFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe,n];
\[Delta]qR[\[Theta]:Except[_String]]:=\[Delta]qRFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe,8];
Format[\[Delta]qR, TraditionalForm]=Style["\[Delta]qR",Bold];


Style[TraditionalForm[Row[{ShowFun[\[Delta]qRe[\[Theta]1,"fRe",n]]}]],Larger]
Style[TraditionalForm[Row[{\[Delta]qRe["\[Theta]1","fRe",n]," = ",\[Delta]qRe[Mod[\[Theta],\[Pi]/6],fRe,n]}]],Larger]
Style[TraditionalForm[Row[{ShowFun[\[Delta]qRe[\[Theta]1,n]]}]],Larger]


Style[TraditionalForm[Row[{ShowFun[\[Delta]qRm[\[Theta]1,\[Delta]qRe,"fRe",n]]}]],Larger]
Style[TraditionalForm[Row[{ShowFun[\[Delta]qRm[\[Theta]1,"\[Delta]qRe",fRe,n]]}]],Larger]
Style[TraditionalForm[Row[{ShowFun[\[Delta]qRm[\[Theta]1,\[Delta]qRe,fRe,n]]}]],Larger]


Style[TraditionalForm[Row[{ShowFun[\[Delta]qR[\[Theta]6,\[Theta]1,"fRe",n]]}]]]


Style[TraditionalForm[Row[{ShowFun[\[Delta]qRm[\[Theta]1,\[Delta]qRe,fRe,n]]}]],Larger]
TraditionalForm[Row[{\[Delta]qR["\[Theta]"]," = ",fRO[\[Delta]qRm[\[Theta]1,\[Delta]qRe,fRe,n],"\!\(\*SubscriptBox[\(\[Theta]\), \(6\)]\)"],"  where  ",Column[{Row[{ "fRe = ",fRe[\[Theta]]}],Row[{TraditionalForm[\[Theta]1]," = ",TraditionalForm[Mod[\[Theta],\[Pi]/6]]}],Row[{TraditionalForm[\[Theta]6]," = ",TraditionalForm[Mod[\[Theta],\[Pi]]]}]}]}]]
Style[TraditionalForm[Row[{ShowFun[\[Delta]qR[\[Theta]6,\[Theta]1,"fRe",n]],"  where  ",Column[{Row[{ "fRe = ",fRe[\[Theta]]}],Row[{TraditionalForm[\[Theta]1]," = ",TraditionalForm[Mod[\[Theta],\[Pi]/6]]}],Row[{TraditionalForm[\[Theta]6]," = ",TraditionalForm[Mod[\[Theta],\[Pi]]]}]}]}]],Larger]


Style[TraditionalForm[Row[{fRe["\[Theta]"]," = ",scale["fR","qR"]\[CircleTimes](qRe["\[Theta]"]+\[Delta]qRe["\[Theta]"])}]],Larger]
Style[TraditionalForm[Row[{fR["\[Theta]"]," = ",scale["fR","qR"]\[CircleTimes](qR["\[Theta]"]+\[Delta]qR["\[Theta]"])}]],Larger]
Style[TraditionalForm[Row[{nLCaCb["\[Theta]"]," = ",scale["nLCaCb","LCaCb"]["\[Theta]"] \[CircleTimes] scale["LCaCb","rR"]["\[Theta]"] \[CircleTimes] scale["rR","fRs"]["\[Theta]"] \[CircleTimes] fSs["\[Theta]"] \[CircleTimes] scale["fR","qR"]\[CircleTimes](qR["\[Theta]"]+\[Delta]qR["\[Theta]"])}]],Larger]


(* ::Subsection::Closed:: *)
(*qRs*)


(* ::Subsubsection::Closed:: *)
(*Matrix*)


qRsFun = Function[{\[Theta]6, \[Theta]1, f, n}, 
    Piecewise[{{
{{1, 1, 1}, 
{-2^(n-2)                       , -Round[2^(n-2)*f[Pi/6 - \[Theta]1]], 2^(n-2) + Round[2^(n-2)*f[Pi/6 - \[Theta]1]]}, 
{-2^(n-2) - Round[2^(n-2)*f[\[Theta]1]] ,  Round[2^(n-2)*f[\[Theta]1]]      , 2^(n-2)}}, 
       Inequality[Pi/6, LessEqual, \[Theta]6, Less, Pi/3]}, 
{{{1, 1, 1}, 
{-2^(n-2), 2^(n-2) + Round[2^(n-2)*f[\[Theta]1]]        , -Round[2^(n-2)*f[\[Theta]1]]}, 
{ 2^(n-2) + Round[2^(n-2)*f[Pi/6 - \[Theta]1]], -2^(n-2), -Round[2^(n-2)*f[Pi/6 - \[Theta]1]]}}, 
       Inequality[Pi/3, LessEqual, \[Theta]6, Less, Pi/2]}, 
{{{1, 1, 1}, 
{ Round[2^(n-2)*f[Pi/6 - \[Theta]1]], -2^(n-2) - Round[2^(n-2)*f[Pi/6 - \[Theta]1]], 2^(n-2)},
{-Round[2^(n-2)*f[\[Theta]1]]       , -2^(n-2)                             , 2^(n-2) + Round[2^(n-2)*f[\[Theta]1]]}}, 
       Inequality[Pi/2, LessEqual, \[Theta]6, Less, (2*Pi)/3]}, 
 {{{1, 1, 1}, 
{2^(n-2) + Round[2^(n-2)*f[Pi/6 - \[Theta]1]], -2^(n-2)                      , -Round[2^(n-2)*f[Pi/6 - \[Theta]1]]}, 
{2^(n-2)                             , -2^(n-2) - Round[2^(n-2)*f[\[Theta]1]], Round[2^(n-2)*f[\[Theta]1]]}}, 
       Inequality[(5*Pi)/6, LessEqual, \[Theta]6, Less,  Pi]}, 
{{{1, 1, 1}, 
{-2^(n-2) - Round[2^(n-2)*f[\[Theta]1]], Round[2^(n-2)*f[\[Theta]1]], 2^(n-2)}, 
{ 2^(n-2),  Round[2^(n-2)*f[Pi/6 - \[Theta]1]], -2^(n-2) - Round[2^(n-2)*f[Pi/6 - \[Theta]1]]}}, 
       Inequality[(2*Pi)/3, LessEqual, \[Theta]6, Less, (5*Pi)/6]}, 
{{{1, 1, 1}, 
{Round[2^(n-2)*f[\[Theta]1]], 2^(n-2), -2^(n-2) - Round[2^(n-2)*f[\[Theta]1]]}, 
{Round[2^(n-2)*f[Pi/6 - \[Theta]1]], -2^(n-2) - Round[2^(n-2)*f[Pi/6 - \[Theta]1]], 2^(n-2)}}, 
       Inequality[0, LessEqual, \[Theta]6, Less, Pi/6]}}, 0]]; 
Clear[qRs]
qRs[\[Theta]6:Except[_String], \[Theta]1_, fReqq_, n_] := qRsFun[\[Theta]6, \[Theta]1, fReqq, n]; 
qRs[\[Theta]:Except[_String], fReqq_, n_] := qRsFun[Mod[\[Theta], Pi], Mod[\[Theta], Pi/6], fReqq, n]; 
qRs[\[Theta]:Except[_String], n_] := qRsFun[Mod[\[Theta], Pi], Mod[\[Theta], Pi/6], fRe, n]; 
qRs[\[Theta]:Except[_String]] := qRsFun[Mod[\[Theta], Pi], Mod[\[Theta], Pi/6], fRe, 8]; 
Format[qRs, TraditionalForm]=Style["qRs",FontWeight->"Bold"];


ShowFun[qRs[\[Theta]6,\[Theta]1,"fRe",n]]


(* ::Subsubsection:: *)
(*Scale*)


scale["qRs","fRs"][\[Theta]:Except[_String],n_:8]:={1,2^(n-2),2^(n-2)};
Format[scale["qRs","fRs"], TraditionalForm]= Superscript[Style["qS",Bold],"-1"];
scale["fRs","qRs"][\[Theta]:Except[_String],n_:8]:={1,2^(2-n),2^(2-n)};
Format[scale["fRs","qRs"], TraditionalForm]=Style["qS",Bold];


Style[TraditionalForm[Row[{qRs["\[Theta]"]," = ",fSs["\[Theta]"]," \[CircleTimes] ",qR["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{fRs["\[Theta]"]," = ",scale["fRs","qRs"]["\[Theta]",n]," \[CircleTimes] ",qRs["\[Theta]"]}]],Larger]
Style[TraditionalForm[Row[{nLCaCb["\[Theta]"]," = ",scale["nLCaCb","LCaCb"]["\[Theta]"]," \[CircleTimes] ",scale["LCaCb","rR"]["\[Theta]"]," \[CircleTimes] ",scale["rR","fRs"]["\[Theta]"]," \[CircleTimes] ",scale["fRs","qRs"]["\[Theta]",n]," \[CircleTimes] ",qRs["\[Theta]"]}]],Larger]




(* ::Subsection::Closed:: *)
(*dqRs*)


(* ::Subsubsection::Closed:: *)
(*Matrix*)


\[Delta]qRsFun=Function[{\[Theta]6, \[Theta]1, f, n},Evaluate[ApplyToPiecewise[Assuming[Element[n,Integers]&&n>3,Simplify[#]]&,
  PiecewiseExpand[ApplyToPiecewise[Times[scale["qR","fR"][\[Theta],n],#]&, fRs[\[Theta]6,\[Theta]1,f]]- qRs[\[Theta]6,\[Theta]1,f,n]]]]];
Clear[\[Delta]qRs]
\[Delta]qRs[\[Theta]6:Except[_String],\[Theta]1_,fReqq_,n_]:=\[Delta]qRsFun[\[Theta]6,\[Theta]1,fReqq,n];
\[Delta]qRs[\[Theta]:Except[_String],fReqq_,n_]:=\[Delta]qRsFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fReqq,n];
\[Delta]qRs[\[Theta]:Except[_String],n_]:=\[Delta]qRsFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe,n];
\[Delta]qRs[\[Theta]:Except[_String]]:=\[Delta]qRsFun[Mod[\[Theta],\[Pi]],Mod[\[Theta],\[Pi]/6],fRe,8];
Format[\[Delta]qRs, TraditionalForm]=Style["\[Delta]qRs",Bold];



ShowFun[\[Delta]qRs[\[Theta]6,\[Theta]1,"fRe",n]]


(* ::Subsection::Closed:: *)
(*dqAS*)


(* ::Subsubsection:: *)
(*Matrix*)


\[Delta]qASFun=Function[{\[Theta]1},Piecewise[{{{1,1,0}, 0 <=  \[Theta]1 < Pi/3}, {{1,0,1}, Pi/3 <=  \[Theta]1 < 2 Pi/3},{{0,1,1}, 2 Pi/3 <=  \[Theta]1 < Pi}},0]];
Clear[\[Delta]qAS]
\[Delta]qAS[\[Theta]:Except[_String]]:=\[Delta]qASFun[Mod[\[Theta],\[Pi]]];
Format[\[Delta]qAS, TraditionalForm]=Style["\[Delta]qAS",Bold];



ShowFun[\[Delta]qAS[\[Theta]1]]


\[Delta]qSFun=Function[{\[Theta]1},{{0,0,0},\[Delta]qASFun[Mod[\[Theta]1+Pi/2,\[Pi]]],\[Delta]qASFun[Mod[\[Theta]1,\[Pi]]]}];
Clear[\[Delta]qS]
\[Delta]qS[\[Theta]:Except[_String]]:=\[Delta]qSFun[\[Theta]];
Format[\[Delta]qS, TraditionalForm]=Style["\[Delta]qS",Bold];



ShowFun[\[Delta]qS[\[Theta]1]]

TraditionalForm[Row[{\[Delta]qS["\!\(\*SubscriptBox[\(\[Theta]\), \(1\)]\)"]," = ",PiecewiseExpand[Assuming[Element[\[Theta]1,Reals]&&\[Theta]1<Pi&&\[Theta]1>=0,FullSimplify[ShowFun[\[Delta]qS[\[Theta]1]]]]]}]]


(* ::Subsection::Closed:: *)
(*dqEO*)


(* ::Subsubsection:: *)
(*Matrix*)


\[Delta]qEOFun=Function[{vec,\[Theta]3},Piecewise[{{vec, 0 <=  \[Theta]3 < Pi/6}, {{vec[[1]],vec[[3]],vec[[2]]}, Pi/6 <=  \[Theta]3 < 2 Pi/3}},0]];
Clear[\[Delta]qEO]
\[Delta]qEO[vec_,\[Theta]:Except[_String]]:=\[Delta]qEOFun[vec, Mod[\[Theta],\[Pi]/3]];
Format[\[Delta]qEO, TraditionalForm]=Style[






\!\(\*OverscriptBox[\("\<\[Delta]qEO\>"\), \(^\)]\),Bold];


ShowFun[\[Delta]qEO[{0,a,b},\[Theta]3]]


\[Delta]qSFun=Function[{\[Theta]1},{{0,0,0},\[Delta]qASFun[Mod[\[Theta]1+Pi/2,\[Pi]]],\[Delta]qASFun[Mod[\[Theta]1,\[Pi]]]}];
Clear[\[Delta]qS]
\[Delta]qS[\[Theta]:Except[_String]]:=\[Delta]qSFun[\[Theta]];
Format[\[Delta]qS, TraditionalForm]=Style["\[Delta]qS",Bold];



ShowFun[\[Delta]qS[\[Theta]1]]

TraditionalForm[Row[{\[Delta]qS["\!\(\*SubscriptBox[\(\[Theta]\), \(1\)]\)"]," = ",PiecewiseExpand[Assuming[Element[\[Theta]1,Reals]&&\[Theta]1<Pi&&\[Theta]1>=0,FullSimplify[ShowFun[\[Delta]qS[\[Theta]1]]]]]}]]


(* ::Subsection::Closed:: *)
(*Combined Scales*)


(* ::Subsubsection::Closed:: *)
(*S : nLCaCb  \[LongLeftArrow] fRs*)


scale["nLCaCb","fRs"][\[Theta]:Except[_String]]:= {1/3,1/2,1/2};
Format[scale["nLCaCb","fRs"], TraditionalForm]=Style["S",Bold];
scale["fRs","nLCaCb"][\[Theta]:Except[_String]]:= {3,2,2};
Format[scale["fRs","nLCaCb"], TraditionalForm]=Superscript[Style["S",Bold],"-1"];


Style[TraditionalForm[Row[{nLCaCb["\[Theta]"]," = ",scale["nLCaCb","fRs"]["\[Theta]"]," \[CircleTimes] ",fRs["\[Theta]"]}]],Larger]


(* ::Subsubsection::Closed:: *)
(*Sq: nLCaCb  \[LongLeftArrow] qRs*)


scale["nLCaCb","qRs"][\[Theta]:Except[_String],n_: 8]:= {1/3,2^(1-n),2^(1-n)};
Format[scale["nLCaCb","qRs"], TraditionalForm]=Subscript[Style["S",Bold],"q"];
scale["qRs","nLCaCb"][\[Theta]:Except[_String],n_: 8]:= {3,2^(3-n),2^(3-n)};
Format[scale["fRs","nLCaCb"], TraditionalForm]=Superscript[Subscript[Style["S",Bold],"q"],"-1"];


Style[TraditionalForm[Row[{nLCaCb["\[Theta]"]," = ",scale["nLCaCb","qRs"]["\[Theta]"]," \[CircleTimes] ",qRs["\[Theta]"]}]],Larger]


(* ::Subsubsection::Closed:: *)
(*Sr : nLCaCb  \[LongLeftArrow] rR*)


scale["nLCaCb","rR"][\[Theta]:Except[_String]]:= {1/3,1/2 Sec[\[Pi]/6-Mod[-(\[Pi]/6)+\[Theta],\[Pi]/3]],1/2 Sec[\[Pi]/6-Mod[\[Theta],\[Pi]/3]]}
Format[scale["nLCaCb","rR"], TraditionalForm]=Subscript[Style["S",Bold],"r"];


Style[TraditionalForm[Row[{nLCaCb["\[Theta]"]," = ",scale["nLCaCb","rR"]["\[Theta]"]," \[CircleTimes] ",rR["\[Theta]"]}]],Larger]


(* ::Subsubsection::Closed:: *)
(*Srq: rR  \[LongLeftArrow] qR*)


scale["rR", "qR"][\[Theta]:Except[_String], n_: 8] := Piecewise[{
   {{1, -(2^(2 - n)*Sin[Pi/6 + \[Theta]]), -(2^(2 - n)*Cos[Pi/6 + \[Theta]])}, Inequality[0,    LessEqual, Mod[\[Theta], Pi/2], Less, Pi/6]},
   {{1,   2^(2 - n)*Cos[\[Theta]],         -(2^(2 - n)*Sin[\[Theta]])},       Inequality[Pi/6, LessEqual, Mod[\[Theta], Pi/2], Less, Pi/3]},
   {{1, -(2^(2 - n)*Sin[Pi/6 - \[Theta]]),   2^(2 - n)*Cos[Pi/6 - \[Theta]]},  Inequality[Pi/3, LessEqual, Mod[\[Theta], Pi/2], Less, Pi/2]}}, Null]
Format[scale["rR", "qR"], TraditionalForm]=Subscript[Style["S",Bold],"r\[LeftArrow]q"];

scale["qR","rR"][\[Theta]:Except[_String],n_:8]:=Piecewise[{
{{1,-(2^(-2+n)*Csc[Pi/6+\[Theta]]),-(2^(-2+n)*Sec[Pi/6+\[Theta]])},Inequality[0,   LessEqual,Mod[\[Theta],Pi/2],Less,Pi/6]},
{{1,  2^(-2+n)*Sec[\[Theta]],      -(2^(-2+n)*Csc[\[Theta]])     },Inequality[Pi/6,LessEqual,Mod[\[Theta],Pi/2],Less,Pi/3]},
{{1,-(2^(-2+n)*Csc[Pi/6-\[Theta]]),  2^(-2+n)*Sec[Pi/6-\[Theta]] },Inequality[Pi/3,LessEqual,Mod[\[Theta],Pi/2],Less,Pi/2]}},Null]
Format[scale["qR","rR"], TraditionalForm]=Superscript[Subscript[Style["S",Bold],"r\[LeftArrow]q"],"-1"];


Style[TraditionalForm[Row[{rR["\[Theta]"]," = ",scale["rR", "qR"]["\[Theta]"]," \[CircleTimes] ",qR["\[Theta]"]}]],Larger]


ShowFun[scale["LCaCb","rR"][\[Theta]]]
ShowFun[scale["nLCaCb","rR"][\[Theta]]]

ShowFun[scale["rR","fR"][\[Theta]]]

ShowFun[scale["rR", "qR"][\[Theta]]]
ShowFun[scale["qR","rR"][\[Theta]]]

ShowFun[scale["qR","fR"][\[Theta]]]
ShowFun[scale["fR","qR"][\[Theta]]]


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


Clear[RGBCube3D];
RGBCube3D[corners:{{_,_,_,_,_,_,_,_},{_,_,_,_,_,_,_,_},{_,_,_,_,_,_,_,_}}]:=RGBCube3D[Transpose[corners]];
RGBCube3D[corners:{{_,_,_},{_,_,_},{_,_,_},{_,_,_},{_,_,_},{_,_,_},{_,_,_},{_,_,_}}]:=Module[{RGBCube,faces,ranges},
ranges =Transpose[{ Map[Min,Transpose[corners]],Map[Max,Transpose[corners]]}];
faces = {{1,2,3,4},{5,6,7,8},{1,2,7,6},{2,3,8,7},{3,4,5,8},{1,4,5,6}};
RGBCube = cubeCorners[{{0,1},{0,1},{0,1}}];
{
Polygon[corners[[faces[[1]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[1]]]]]]],
Polygon[corners[[faces[[2]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[2]]]]]]],
Polygon[corners[[faces[[3]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[3]]]]]]],
Polygon[corners[[faces[[4]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[4]]]]]]],
Polygon[corners[[faces[[5]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[5]]]]]]],
Polygon[corners[[faces[[6]]]],VertexColors->MapThread[RGBColor,Transpose[Transpose[RGBCube][[faces[[6]]]]]]]}
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
{Opacity[If[r+g+b < n cut, opacity[[1]], opacity[[2]] ]],color,
Sphere[rgbCenter,radius]},{b,0,n-1},{g,0,n-1},{r,0,n-1}]]
]


(* ::Subsection:: *)
(*LCaCb Cube*)


LCaCbAxisRanges[\[Theta]_]:={{0,Sqrt[3]},{-Sqrt[(2/3)] Cos[\[Pi]/6-Mod[\[Theta] -Pi/6,Pi/3]] ,Sqrt[2/3] Cos[\[Pi]/6-Mod[\[Theta] -Pi/6,Pi/3]]},{-Sqrt[(2/3)] Cos[\[Pi]/6-Mod[\[Theta],Pi/3]] ,Sqrt[2/3] Cos[\[Pi]/6-Mod[\[Theta],Pi/3]]}}


LCaCbAxisLengths = Function[{\[Theta]},Evaluate[Flatten[LCaCbAxisRanges[\[Theta]][[All,2]] - LCaCbAxisRanges[\[Theta]][[All,1]]]]];


LCaCbCube["LCaCb"][\[Theta]_]:=cubeCorners[LCaCbAxisRanges[\[Theta]]];
LCaCbCube["RGB"]=Function[{\[Theta]},Evaluate[TrigFactor[FullSimplify[TrigToExp[iLCaCb[\[Theta]].LCaCbCube["LCaCb"][\[Theta]]]]]]];


(* ::Subsubsection:: *)
(*Color*)


(*SetUpLCaCbColor[\[Theta]_] :=Module[{theta}, 
DownValues[LCaCbColorTheta] = HoldPattern[LCaCbColorTheta]:>\[Theta];
LCaCbColorFastList=Compile[{{yIn, _Real},{aIn, _Real},{bIn, _Real}}, Module[{y,a,b,h,s,angle},
{Quiet[Mod[(ArcTan[(aIn-0.5),(bIn-0.5)]-theta-4 Pi/3),2 Pi]/(2 Pi)/.Indeterminate->0,{ArcTan::indet}],
Sqrt[2]*Sqrt[(aIn-0.5)^2+(bIn-0.5)^2],
yIn}
]]/.{theta -> \[Theta]};
LCaCbColorFast=Hue[LCaCbColorFastList[##]]&;
]*)


(*LCaCbColorTheta/: Set[LCaCbColorTheta,\[Theta]_]:=SetUpLCaCbColor[\[Theta]];
LCaCbColorTheta = 0;*)


(*Clear[LCaCbColorFastTheta]
LCaCbColorFastTheta[yIn_,aIn_,bIn_,\[Theta]In_]:= Module[{y,a,b,h,s,angle},
y=yIn; a = aIn-0.5; b= bIn-0.5;
Quiet[{s, angle}=CoordinateTransform[{"Cartesian"->"Polar",2},{a,b}]/.Indeterminate->0,{ArcTan::indet}];
angle = angle-\[Theta]In-4 Pi/3 +2 Pi;h=angle/(2 Pi) ; s = Sqrt[2]*s; 
Hue[h,s,y]
];*)


(*LCaCbColor[yab:{_,_,_}]:=Module[{y,a,b,h,s,angle},
  LCaCbColorFast[     yab[[1]],yab[[2]],yab[[3]]]
]
LCaCbColor[yab:{_,_,_,_}]:=Module[{y,a,b,h,s,angle},
  h=LCaCbColorFastList[     yab[[1]],yab[[2]],yab[[3]]];
Hue[Sequence@@h,yab[[4]] ]
]
LCaCbColor[yab_,\[Theta]_]:=Module[{y,a,b,h,s,angle},
If[TrueQ[LCaCbColorTheta==\[Theta]],
  LCaCbColorFast[     yab[[1]],yab[[2]],yab[[3]]],
  LCaCbColorFastTheta[yab[[1]],yab[[2]],yab[[3]],\[Theta]]
]]*)


Clear[LCaCbColorFast]
LCaCbColorFast["Hue"][\[Theta]_,yIn_,aIn_,bIn_,lIn___]:= Module[{},
Hue[Quiet[Mod[(ArcTan[(aIn-0.5),(bIn-0.5)]-\[Theta]-4 Pi/3),2 Pi]/(2 Pi)/.Indeterminate->0,{ArcTan::indet}],
Sqrt[2]*Sqrt[(aIn-0.5)^2+(bIn-0.5)^2],
yIn,lIn]
]
LCaCbColorFast["RGB"][\[Theta]_,yIn_,aIn_,bIn_,lIn___]:= Module[{},
ColorConvert[Hue[Quiet[Mod[(ArcTan[(aIn-0.5),(bIn-0.5)]-\[Theta]-4 Pi/3),2 Pi]/(2 Pi)/.Indeterminate->0,{ArcTan::indet}],
Sqrt[2]*Sqrt[(aIn-0.5)^2+(bIn-0.5)^2],
yIn,lIn],"RGB"]
]
LCaCbColorFast[colorSpace_][\[Theta]_,yIn_,aIn_,bIn_,lIn___]:= Module[{},
ColorConvert[Hue[Quiet[Mod[(ArcTan[(aIn-0.5),(bIn-0.5)]-\[Theta]-4 Pi/3),2 Pi]/(2 Pi)/.Indeterminate->0,{ArcTan::indet}],
Sqrt[2]*Sqrt[(aIn-0.5)^2+(bIn-0.5)^2],
yIn,lIn],colorSpace]
]
Clear[SetUpLCaCbColor]
SetUpLCaCbColor[name_:"LCaCbColorFast",\[Theta]_,colorSpace_:"Hue"] :=Module[{fun},
fun=Function[{yy,aa,bb,\[Alpha]\[Alpha]},Evaluate[LCaCbColorFast[colorSpace][\[Theta],yy,aa,bb,\[Alpha]\[Alpha]]]];
LCaCbColor[List[elem__]]:=LCaCbColor[elem];
ToExpression[name<>"[List[elem__]] := "<>name<>"[elem]"];
ToExpression[name<>"[yyy_,aaa_,bbb_,\[Alpha]\[Alpha]\[Alpha]\[Alpha]_] := Quiet["<>ToString[fun[yyy,aaa,bbb,\[Alpha]\[Alpha]\[Alpha]\[Alpha]],InputForm]<>"/.Indeterminate->0,{ArcTan::indet}]"];
ToExpression[name<>"[yyy_,aaa_,bbb_] := Quiet[("<>ToString[fun[yyy,aaa,bbb,Null],InputForm]<>")/.{Indeterminate->0, Null\[Rule]Sequence[]},{ArcTan::indet}]"];
]


(* ::Input:: *)
(*Block[{\[Theta]=4,LCaCb},SetUpLCaCbColor["LCaCb",\[Theta],"Hue"];Row[{Graphics[{Black,Rectangle[{-1,0.25},{0.25,1.5}],Rectangle[{0.25,-1},{1.5,0.25}],Opacity[0.6],LCaCb[0.7,0.7,0.1],Disk[{0.5,0.5},1],Opacity[0.5],LCaCb[0.7,0.1,0.7],Disk[]}],*)
(*Graphics[{Black,Rectangle[{-1,0.25},{0.25,1.5}],Rectangle[{0.25,-1},{1.5,0.25}],LCaCb[0.7,0.7,0.1,0.6],Disk[{0.5,0.5}],LCaCb[0.7,0.1,0.7,0.5],Disk[]}]}]*)
(*]*)


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
LCaCbinRGBCubeCorners =Transpose[cubeCorners[ Map[{Min[#],Max[#]}&,iLCaCb[\[Theta]]. cubeCorners[ LCaCbAxisRanges[\[Theta]]]]]];
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
RGBCubeCorners    = Transpose[cubeCorners[{{0,1},{0,1},{0,1}}]];
LCaCbCubeCorners  = Transpose[cubeCorners[ LCaCbAxisRanges[\[Theta]]]];
LCaCbinRGBCubeCorners = Transpose[cubeCorners[ Map[{Min[#],Max[#]}&,iLCaCb[\[Theta]]. cubeCorners[ LCaCbAxisRanges[\[Theta]]]]]];
(*LCaCbinRGBCubeCorners = Transpose[cubeCorners[ iLCaCb[\[Theta]]. cubeCorners[ LCaCbAxisRanges[\[Theta]]]]];*)
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


(* ::Subsection::Closed:: *)
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


(* ::Section::Closed:: *)
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


(* ::Section::Closed:: *)
(*Text Display*)


MatrixFormCubeColor[mat_,forgroundWhite_:1,backgroundWhite_:1]:=Module[{fg,bg },fg = forgroundWhite; bg={backgroundWhite,backgroundWhite-1};MatrixForm[{
MapThread[Style[#1,#2,Background->#3]&, {mat[[1]],Map[RGBColor,fg Transpose[RGBCube["RGB"]]],Map[RGBColor,bg[[1]]-bg[[2]] Transpose[RGBCube["RGB"]]]}],MapThread[Style[#1,#2,Background->#3]&, {mat[[2]],Map[RGBColor,fg Transpose[RGBCube["RGB"]]],Map[RGBColor,bg[[1]]-bg[[2]] Transpose[RGBCube["RGB"]]]}],MapThread[Style[#1,#2,Background->#3]&, {mat[[3]],Map[RGBColor,fg Transpose[RGBCube["RGB"]]],Map[RGBColor,bg[[1]]-bg[[2]] Transpose[RGBCube["RGB"]]]}]}]]


colorMat[mat_]:=Module[{pos,out}, 
pos=Position[Sign[mat],1];out=MapAt[Style[#,Red]&,mat,pos]; 
pos=Position[Sign[mat],-1];out=MapAt[Style[#,Blue]&,out,pos];
pos=Position[matSameSign[mat],1];out=MapAt[Framed[#]&,out,pos];
 out];


mForm[mat_List]:=ToString[MatrixForm[mat],TraditionalForm];
mForm[a_,b__]:=ToString[MatrixForm[List[a,b]],TraditionalForm];


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


(* ::Section::Closed:: *)
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


(* ::Section::Closed:: *)
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


(* ::Section:: *)
(*Normal Distribution Function*)


(* ::Subsection:: *)
(*Distro Parameters*)


togButton[var_]:=Button[Dynamic[Style[var,If[show[var],Directive[ Darker[Green],Bold], Black]]], show[var] =  If[show[var],False,True,True], Appearance -> None, 
    Evaluator -> Automatic, Method -> "Preemptive", ContentPadding -> True]
togButton[var_,txt_]:=Button[Dynamic[Style[txt,If[show[var],Directive[ Darker[Green],Bold], Black]]], show[var] =  If[show[var],False,True,True], Appearance -> None, 
    Evaluator -> Automatic, Method -> "Preemptive", ContentPadding -> True]
setUnitButton=Button[Style["0-1",Bold,Small], 
show["\[Mu]"]=True;  show["\[Sigma]"]=True;   show["\[Gamma]"]=True;
show["c"]=False;show["s"]=False;show["g"]=False;, Appearance -> None, 
    Evaluator -> Automatic, Method -> "Preemptive", ContentPadding -> True];
setRangeButton[min_,max_]:=Button[Style[StringJoin[ToString[min]," - ",ToString[max]],Bold,Small], 
show["\[Mu]"]=False;show["\[Sigma]"]=False; show["\[Gamma]"]=False;
show["c"]=True;  show["s"]=True;    show["g"]=True;, Appearance -> None, 
    Evaluator -> Automatic, Method -> "Preemptive", ContentPadding -> True]


Clear[pointToUnit]
pointToUnit[pnt:Except[_List],{min:Except[_List],max:Except[_List]}]:=(pnt-min)/(max-min)
pointToUnit[{pnt_,restPnt__},{{min_,max_},restRanges__}]:=Flatten[{pointToUnit[pnt,{min,max}],pointToUnit[{restPnt},{restRanges}]}]
pointToUnit[{pnt_},{{min_,max_}}]:={pointToUnit[pnt,{min,max}]}


Clear[pointFromUnit]
pointFromUnit[pnt:Except[_List],{min:Except[_List],max:Except[_List]}]:=(max-min)pnt+min
pointFromUnit[{pnt_,restPnt__},{{min_,max_},restRanges__}]:=Flatten[{pointFromUnit[pnt,{min,max}],pointFromUnit[{restPnt},{restRanges}]}]
pointFromUnit[{pnt_},{{min_,max_}}]:={pointFromUnit[pnt,{min,max}]}


Clear[scaleToUnit]
scaleToUnit[pnt:Except[_List],{min:Except[_List],max:Except[_List]}]:=(pnt)/(max-min)
scaleToUnit[{pnt_,restPnt__},{{min_,max_},restRanges__}]:=Flatten[{pointToUnit[pnt,{min,max}],pointToUnit[{restPnt},{restRanges}]}]
scaleToUnit[{pnt_},{{min_,max_}}]:={pointToUnit[pnt,{min,max}]}


Clear[scaleFromUnit]
scaleFromUnit[pnt:Except[_List],{min:Except[_List],max:Except[_List]}]:=(pnt)(max-min)
scaleFromUnit[{pnt_,restPnt__},{{min_,max_},restRanges__}]:=Flatten[{scaleFromUnit[pnt,{min,max}],scaleFromUnit[{restPnt},{restRanges}]}]
scaleFromUnit[{pnt_},{{min_,max_}}]:={scaleFromUnit[pnt,{min,max}]}


gradientFromUnit[pnt:Except[_List],{{minX:Except[_List],maxX:Except[_List]},{minY:Except[_List],maxY:Except[_List]}}]:=pnt (maxY-minY)/(maxX-minX)
 gradientToUnit[pnt:Except[_List],{{minX:Except[_List],maxX:Except[_List]},{minY:Except[_List],maxY:Except[_List]}}]:=pnt (maxX-minX)/(maxY-minY)


show["c"]=False;show["g"]=False; show["dRange"]=True;
show["s"]=False;show["\[Gamma]"]=True;   show["\[Mu]"]=True;show["\[Sigma]"]=True;
Clear[DynamicDistroPanel];

layout[sliders_,selector_,output_]:=Panel[Column[{sliders,Row[{Panel[selector,ImageSize->Scaled[.2],Alignment->Center],"   ",Panel[output[[1]],ImageSize->Scaled[0.7],Alignment->Center]}]
},Center],ImageSize->Scaled[0.6]];

DynamicDistroPanel[funcs_List,layoutFun_:layout]:=DynamicModule[{\[Mu]=0.5,c=128,\[Sigma]=8/51,s=40,\[Gamma]=51/(8 Sqrt[2]),g=1/(40 Sqrt[2]),sMin=0,sMax=255,dMin=0,dMax=255,sRange,dRange,s\[CapitalDelta],d\[CapitalDelta],\[Kappa],\[Delta],m,\[Omega],\[CapitalOmega],\[Lambda],L,center,fun,sliders,selector,output},
sMin=0;sMax=255;
dMin=0;dMax=255;
{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}];
ssMin=1/2; ssMax=3/2 255 ;
{{\[Mu]Min,cMin},{\[Sigma]Min,ssMin},{\[Gamma]Max,gMax}}=N[setDistroValues[{{0,sMin},{\[Sigma]Min,ssMin},{\[Gamma]Max,1}},{{sMin,sMax},{dMin,dMax}},Unit->False,G->False]];
{{\[Mu]Max,cMax},{\[Sigma]Max,ssMax},{\[Gamma]Min,gMin}}=N[setDistroValues[{{1,sMax},{\[Sigma]Max,ssMax},{\[Gamma]Max,gMax}},{{sMin,sMax},{dMin,dMax}},Unit->False,G->False]];

sliders=Dynamic[Column[ReplaceRepeated[{
If[show["\[Mu]"],ValueThumbSlider[Dynamic[{\[Mu]},(\[Mu]=#1;{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=N[setDistroValues[{{#1,c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}},Unit->True,G->False]];{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}])&],{\[Mu]Min,\[Mu]Max,N[1/255]}],Null],
If[show["c"],ValueThumbSlider[Dynamic[{sMin,c,sMax},(sMin=#1;sMax=#3;{{\[Mu]Min,cMin},{\[Sigma]Min,ssMin},{\[Gamma]Max,gMax}}=N[setDistroValues[{{0,#1},{\[Sigma]Min,ssMin},{\[Gamma]Max,1}},{{#1,#3},{dMin,dMax}},Unit->False,G->True]];
{{\[Mu]Max,cMax},{\[Sigma]Max,ssMax},{\[Gamma]Min,gMin}}=N[setDistroValues[{{1,#3},{\[Sigma]Max,ssMax},{\[Gamma]Max,gMax}},{{#1,#3},{dMin,dMax}},Unit->True,G->False]];{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=N[setDistroValues[{{\[Mu],#2},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}},Unit->False,G->False]];{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}])&],{0,255,1}],Null],
If[show["dRange"],ValueThumbSlider[Dynamic[{dMin,dMax},(dMin=#1;dMax=#2;{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}])&],{0,255,1}],Null],
If[show["\[Sigma]"],ValueThumbSlider[Dynamic[{\[Sigma]},(\[Sigma]=#1;{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=N[setDistroValues[{{\[Mu],c},{#1,s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}},Unit->True,G->False]];{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}])&],{Dynamic[\[Sigma]Min],Dynamic[\[Sigma]Max]}],Null],
If[show["s"],ValueThumbSlider[Dynamic[{s},(s=#1;{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=N[setDistroValues[{{\[Mu],c},{\[Sigma],#1},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}},Unit->False,G->False]];{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}])&],{Dynamic[ssMin],Dynamic[ssMax]}],Null],
If[show["\[Gamma]"],ValueThumbSlider[Dynamic[{\[Gamma]},(\[Gamma]=#1;{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=N[setDistroValues[{{\[Mu],c},{\[Sigma],s},{#1,g}},{{sMin,sMax},{dMin,dMax}},Unit->True,G->True]];{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}])&],{Dynamic[\[Gamma]Min],Dynamic[\[Gamma]Max]}],Null],
If[show["g"],ValueThumbSlider[Dynamic[{g},(g=#1;{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=N[setDistroValues[{{\[Mu],c},{\[Sigma],s},{\[Gamma],#1}},{{sMin,sMax},{dMin,dMax}},Unit->False,G->True]];{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}])&],{Dynamic[gMin],Dynamic[gMax]}],Null]},{x___,Null,y___}:>{x,y}]]];
selector= Dynamic[Grid[{{togButton["dRange","dst"],setUnitButton,setRangeButton[sMin,sMax]},{"Mean",togButton["\[Mu]"],togButton["c"]},{"Std",togButton["\[Sigma]"],togButton["s"]},{"G",togButton["\[Gamma]"],togButton["g"]}},Dividers->{{2->Black},{2->Black}}]];
output =Map[Dynamic[# [{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}, {{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],L},{\[Omega],\[CapitalOmega]}}]]&,funcs];
;
layoutFun[sliders,selector,output]]
DynamicDistroPanel[funcs_Function,layoutFun_:layout]:=DynamicDistroPanel[{funcs},layoutFun];


dis[ x_,s_,c_,sMin_,sMax_,dMin_,dMax_]:=dMin+((dMax-dMin) (Erf[(c-sMin)/(Sqrt[2] s)]-Erf[(c-x)/(Sqrt[2] s)]))/(-Erf[(c-sMax)/(Sqrt[2] s)]+Erf[(c-sMin)/(Sqrt[2] s)])


eErf[ x_,g_,c_,xMin_,xMax_,yMin_,yMax_]:=yMin+((-yMax+yMin)*(Erf[(g*(-c+x))]+Erf[(g*(c-xMin))]))/(Erf[(g*(c-xMax))]+Erf[(g*(-c+xMin))])


Clear[gradC];
gradC[ g_,c_,sMin_,sMax_,dMin_,dMax_]:=(2 (-dMax+dMin) g)/(Sqrt[\[Pi]] (Erf[g (c-sMax)]+Erf[g (-c+sMin)]));


Clear[uUnitGrad]
uUnitGrad[ \[Sigma]_,\[Mu]_,{{sMin_,sMax_},{dMin_,dMax_}}]:= 
{\[Mu]-\[Sigma] Sqrt[Log[2/\[Pi]]+2 Log[(dMax-dMin)/(sMax-sMin )]-2 Log[\[Sigma] (Erf[\[Mu]/(Sqrt[2] \[Sigma])]-Erf[(\[Mu] - 1)/(Sqrt[2] \[Sigma])])]],\[Mu]+\[Sigma] Sqrt[Log[2/\[Pi]]+2 Log[(dMax-dMin)/(sMax-sMin )]-2 Log[\[Sigma] (Erf[\[Mu]/(Sqrt[2] \[Sigma])]-Erf[(\[Mu] - 1)/(Sqrt[2] \[Sigma])])]]}


uUnitGradCond[ \[Gamma]_,\[Mu]_,{{sMin_,sMax_},{dMin_,dMax_}}]:= 
(2 \[Gamma])/(Sqrt[\[Pi]] (Erf[\[Gamma] \[Mu]]+Erf[\[Gamma]-\[Gamma] \[Mu]]))>=  (sMax-sMin)/(dMax-dMin)


uErfLowHigh[ \[Gamma]_,\[Mu]_,{{sMin_,sMax_},{dMin_,dMax_}}]:={\[Mu]+InverseErf[((1-dMax+dMin) Erf[\[Gamma] \[Mu]]+Erf[\[Gamma]-\[Gamma] \[Mu]])/(dMax-dMin)]/\[Gamma],\[Mu]+InverseErf[(-Erf[\[Gamma] \[Mu]]+(-1+dMax-dMin) Erf[\[Gamma]-\[Gamma] \[Mu]])/(dMax-dMin)]/\[Gamma]}


uG[\[Sigma]_]:= 1/(Sqrt[2] \[Sigma]) 


Clear[\[Mu],\[Sigma],t]
peakNormedNormalDistribution=Function[{\[Mu],\[Sigma],t},Evaluate[PDF[NormalDistribution[\[Mu],\[Sigma]],t]/PDF[NormalDistribution[\[Mu],\[Sigma]],\[Mu]]]];


valTable=Function[{vars,ranges},Block[{\[Mu],c,\[Sigma],s,\[Gamma],g,sMin,sMax,sRange,dMin,dMax,dRange,s\[CapitalDelta],d\[CapitalDelta],\[Kappa],\[Delta],m,\[Omega],\[CapitalOmega],\[Lambda],L},
{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=vars;
{{sMin,sMax},{dMin,dMax}}=ranges;TableForm[{
{Row[{"\[Mu] = ",NumberForm[\[Mu],4]}],Row[{"c = ",NumberForm[c,4]}]},{Row[{"\[Sigma] = ",NumberForm[\[Sigma],4]}],Row[{"s = ",NumberForm[s,4]}]},{Row[{"\[Gamma] = ",NumberForm[\[Gamma],4]}],Row[{"g = ",NumberForm[g,4]}]}},TableHeadings->{{"Mean","Std","G"},{"0-1",StringJoin[ToString[sMin]," - ",ToString[sMax]]}}]]
];
tableGammaFuncs=Function[{vars,ranges},Block[{\[Mu],c,\[Sigma],s,\[Gamma],g,sMin,sMax,sRange,dMin,dMax,dRange,s\[CapitalDelta],d\[CapitalDelta],\[Kappa],\[Delta],m,\[Omega],\[CapitalOmega],\[Lambda],L},
{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=vars;
{{sMin,sMax},{dMin,dMax}}=ranges;Grid[{{
Plot[peakNormedNormalDistribution[pointToUnit[c,{sMin,sMax}],scaleToUnit[s,{sMin,sMax}],t],{t,0,1},PlotRange->{{0,1},Automatic},ImageSize->{200,200}],
Plot[peakNormedNormalDistribution[c,s,t],{t,sMin,sMax},PlotRange->{{sMin,sMax},All},ImageSize->{200,200}]},{Plot[PDF[NormalDistribution[pointToUnit[c,{sMin,sMax}],scaleToUnit[s,{sMin,sMax}]],t],{t,0,1},PlotRange->{{0,1},Automatic},ImageSize->{200,200}],
Plot[PDF[NormalDistribution[c,s],t],{t,sMin,sMax},PlotRange->{{sMin,sMax},All},ImageSize->{200,200}]}}]
]];



(* ::Subsection:: *)
(*Distro Plots*)


(*Clear[setDistroValues]
Options[setDistroValues]={Unit->True,G->True};
setDistroValues[ \[Sigma]g_,\[Mu]c_,{{sMin_,sMax_},{dMin_,dMax_}},OptionsPattern[]]:= Module[{\[Mu],c,\[Sigma],s,\[Gamma],g},
If[OptionValue[Unit],
\[Mu]=\[Mu]c ;c = pointFromUnit[\[Mu]c ,{sMin,sMax}];
If[OptionValue[G],
\[Gamma]=\[Sigma]g; \[Sigma] = uG[\[Gamma]]; s=scaleFromUnit[\[Sigma],{sMin,sMax}]; g = uG[s]; ,
\[Sigma] =\[Sigma]g;\[Gamma] = uG[\[Sigma] ];s=scaleFromUnit[\[Sigma],{sMin,sMax}]; g = uG[s];
],
\[Mu]=pointToUnit[\[Mu]c ,{sMin,sMax}] ;c = \[Mu]c;
If[OptionValue[G],
g=\[Sigma]g;  s = uG[g];\[Sigma]=scaleToUnit[s,{sMin,sMax}];\[Gamma] = uG[\[Sigma] ];,
s =\[Sigma]g; g = uG[s]; \[Sigma]=scaleToUnit[s,{sMin,sMax}];\[Gamma] = uG[\[Sigma] ];
];
];
{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}
]
setDistroValues[ {{\[Mu]i_,ci_},{\[Sigma]i_,si_},{\[Gamma]i_,gi_}},{{sMin_,sMax_},{dMin_,dMax_}},OptionsPattern[]]:= Module[{\[Mu],c,\[Sigma],s,\[Gamma],g},
If[OptionValue[Unit],
\[Mu]=\[Mu]i ;c = pointFromUnit[\[Mu]i ,{sMin,sMax}];
If[OptionValue[G],
\[Gamma]=\[Gamma]i; \[Sigma] = uG[\[Gamma]]; s=scaleFromUnit[\[Sigma],{sMin,sMax}]; g = uG[s]; ,
\[Sigma] =\[Sigma]i;\[Gamma] = uG[\[Sigma] ];s=scaleFromUnit[\[Sigma],{sMin,sMax}]; g = uG[s];
],
\[Mu]=pointToUnit[ci ,{sMin,sMax}] ;c = ci;
If[OptionValue[G],
g=gi;  s = uG[g];\[Sigma]=scaleToUnit[s,{sMin,sMax}];\[Gamma] = uG[\[Sigma] ];,
s =si; g = uG[s]; \[Sigma]=scaleToUnit[s,{sMin,sMax}];\[Gamma] = uG[\[Sigma] ];
];
];
{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}
]*)


Clear[DistroValues]
Options[DistroValues]={Unit->True,G->True};
DistroValues[ \[Sigma]g_,\[Mu]c_,{{sMin_,sMax_},{dMin_,dMax_}},OptionsPattern[]]:= Module[{\[Mu],c,\[Sigma],s,\[Gamma],g},
If[OptionValue[Unit],
\[Mu] = \[Mu]c; c = pointFromUnit[\[Mu]c ,{sMin,sMax}];
If[OptionValue[G],
\[Gamma] = \[Sigma]g; \[Sigma] = uG[\[Gamma]]; s = scaleFromUnit[\[Sigma],{sMin,sMax}]; g = uG[s]; ,
\[Sigma] = \[Sigma]g; \[Gamma] = uG[\[Sigma]]; s = scaleFromUnit[\[Sigma],{sMin,sMax}]; g = uG[s];
],
\[Mu]=pointToUnit[\[Mu]c ,{sMin,sMax}] ;c = \[Mu]c;
If[OptionValue[G],
g = \[Sigma]g; s = uG[g]; \[Sigma] = scaleToUnit[s,{sMin,sMax}]; \[Gamma] = uG[\[Sigma] ];,
s = \[Sigma]g; g = uG[s]; \[Sigma] = scaleToUnit[s,{sMin,sMax}]; \[Gamma] = uG[\[Sigma] ];
];
];
{"\[Mu]" -> \[Mu] ,"c" -> c,"\[Sigma]" -> \[Sigma],"s" -> s,"\[Gamma]" -> \[Gamma],"g" -> g,"sMin"->sMin,"sMax"->sMax,"dMin"->dMin,"dMax"->dMax,"sRange"->(sMax-sMin),"dRange"->(dMax-dMin)}
]
DistroValues[ {{\[Mu]i_,ci_},{\[Sigma]i_,si_},{\[Gamma]i_,gi_}},{{sMin_,sMax_},{dMin_,dMax_}},OptionsPattern[]]:= Module[{\[Mu],c,\[Sigma],s,\[Gamma],g},
If[OptionValue[Unit],
\[Mu] = \[Mu]i; c = pointFromUnit[\[Mu]i ,{sMin,sMax}];
If[OptionValue[G],
\[Gamma] =\[Gamma]i; \[Sigma] = uG[\[Gamma]]; s = scaleFromUnit[\[Sigma],{sMin,sMax}]; g = uG[s]; ,
\[Sigma] =\[Sigma]i; \[Gamma] = uG[\[Sigma]]; s = scaleFromUnit[\[Sigma],{sMin,sMax}]; g = uG[s];
],
\[Mu]=pointToUnit[ci ,{sMin,sMax}] ;c = ci;
If[OptionValue[G],
g = gi; s = uG[g]; \[Sigma] = scaleToUnit[s,{sMin,sMax}]; \[Gamma] = uG[\[Sigma] ];,
s = si; g = uG[s]; \[Sigma] = scaleToUnit[s,{sMin,sMax}]; \[Gamma] = uG[\[Sigma] ];
];
];
{"\[Mu]" -> \[Mu] ,"c" -> c,"\[Sigma]" -> \[Sigma],"s" -> s,"\[Gamma]" -> \[Gamma],"g" -> g,
"sMin"->sMin, "sMax"->sMax, "dMin"->dMin, "dMax"->dMax, "sRange"->(sMax-sMin), "dRange"->(dMax-dMin)}
]


Clear[setDistroValues]
Unit::usage = "Option for setDistroValues. If the input values are in the unit space. True/False";
G::usage = "If the standard deviation information is given as a standard deviation or the reciprical G representation. True/False";
Options[setDistroValues]={Unit->True,G->True};
setDistroValues[ \[Sigma]g_,\[Mu]c_,{{sMin_,sMax_},{dMin_,dMax_}},opts:OptionsPattern[]]:= Module[{\[Mu],c,\[Sigma],s,\[Gamma],g},
{{"\[Mu]","c"},{"\[Sigma]","s"},{"\[Gamma]","g"}}/.DistroValues[ \[Sigma]g, \[Mu]c, {{sMin,sMax},{dMin,dMax}},opts]
]
setDistroValues[ {{\[Mu]i_,ci_},{\[Sigma]i_,si_},{\[Gamma]i_,gi_}},{{sMin_,sMax_},{dMin_,dMax_}},opts:OptionsPattern[]]:= Module[{\[Mu],c,\[Sigma],s,\[Gamma],g},
{{"\[Mu]","c"},{"\[Sigma]","s"},{"\[Gamma]","g"}}/.DistroValues[ {{\[Mu]i,ci},{\[Sigma]i,si},{\[Gamma]i,gi}},{{sMin,sMax},{dMin,dMax}},opts]
]


(* ::Text:: *)
(*Set Sensible min and Max ranges for the parameters.*)


sMin=0;sMax=255;
dMin=0;dMax=255;
ssMin=1/2; ssMax=3/2 255 ;
{{\[Mu]Min,cMin},{\[Sigma]Min,ssMin},{\[Gamma]Max,gMax}}=N[setDistroValues[{{0,sMin},{\[Sigma]Min,ssMin},{\[Gamma]Max,1}},{{sMin,sMax},{dMin,dMax}},Unit->False,G->False]];
{{\[Mu]Max,cMax},{\[Sigma]Max,ssMax},{\[Gamma]Min,gMin}}=N[setDistroValues[{{1,sMax},{\[Sigma]Max,ssMax},{\[Gamma]Max,gMax}},{{sMin,sMax},{dMin,dMax}},Unit->False,G->False]];



Clear[DistroParams]
DistroParams[ {{\[Mu]_,c_},{\[Sigma]_,s_},{\[Gamma]_,g_}},{{sMin_,sMax_},{dMin_,dMax_}}]:= Module[{sRange,dRange,s\[CapitalDelta],d\[CapitalDelta],K,\[Delta],m,\[Omega],\[CapitalOmega],\[Lambda],\[CapitalLambda]},
{sRange,dRange} = {sMax-sMin, dMax-dMin};
K = sRange/dRange;
\[Delta]=(2  \[Gamma])/(Sqrt[\[Pi]]  (Erf[\[Gamma] \[Mu]]+Erf[\[Gamma](1- \[Mu])]));
m = gradientFromUnit[\[Delta], {{sMin, sMax},{dMin, dMax}}];
{s\[CapitalDelta],d\[CapitalDelta]}={1/sRange,1/dRange};
\[Lambda]={\[Mu]-1/\[Gamma] InverseErf[(1-d\[CapitalDelta]) Erf[\[Gamma] \[Mu]]-d\[CapitalDelta] Erf[\[Gamma](1-\[Mu])]],\[Mu]+1/\[Gamma] InverseErf[- d\[CapitalDelta] Erf[\[Gamma] \[Mu]]+(1-d\[CapitalDelta]) Erf[\[Gamma](1-\[Mu])]]};
\[CapitalLambda]=pointFromUnit[\[Lambda],{{sMin,sMax},{sMin,sMax}}];
If[TrueQ[\[Delta] < K],
\[Omega]={};\[CapitalOmega] ={},
\[Omega] ={\[Mu]-1/\[Gamma] Sqrt[Log[\[Delta]/K]],\[Mu]+1/\[Gamma] Sqrt[Log[\[Delta]/K]]};
\[CapitalOmega] =pointFromUnit[\[Omega],{{sMin,sMax},{sMin,sMax}}]
];
{"sRange"->sRange,"dRange"->dRange,"K"->K,"\[Delta]"->\[Delta],"m"->m,"\[Omega]"->\[Omega],"\[CapitalOmega]"->\[CapitalOmega],"\[Lambda]"->\[Lambda],"\[CapitalLambda]"->\[CapitalLambda]}
]


Clear[setDistroParams]
setDistroParams[ {{\[Mu]_,c_},{\[Sigma]_,s_},{\[Gamma]_,g_}},{{sMin_,sMax_},{dMin_,dMax_}}]:= Module[{sRange,dRange,s\[CapitalDelta],d\[CapitalDelta],K,\[Delta],m,\[Omega],\[CapitalOmega],\[Lambda],\[CapitalLambda]},
{{"sRange","dRange","K"},{"\[Delta]","m"},{"\[Lambda]","\[CapitalLambda]"},{"\[Omega]","\[CapitalOmega]"}}/.DistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}]
]


Clear[DistroAll]
DistroAll[ \[Sigma]s\[Gamma]g_,\[Mu]c_,{{sMin_,sMax_},{dMin_,dMax_}},opts:OptionsPattern[]]:= Module[{x,\[Mu],c,\[Sigma],s,\[Gamma],g,sRange,dRange,K,\[Delta],m,\[Lambda],\[CapitalLambda],\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,linear,shift,dis,disFunc,linearExtensionFunc},
{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}= {{"\[Mu]","c"},{"\[Sigma]","s"},{"\[Gamma]","g"}}/.DistroValues[ \[Sigma]s\[Gamma]g, \[Mu]c, {{sMin,sMax},{dMin,dMax}},opts];
{{sRange,dRange,K},{\[Delta],m},{\[Lambda],\[CapitalLambda]},{\[Omega],\[CapitalOmega]}}={{"sRange","dRange","K"},{"\[Delta]","m"},{"\[Lambda]","\[CapitalLambda]"},{"\[Omega]","\[CapitalOmega]"}}/.DistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}];

disFunc=Function[{x},Evaluate[dMin-dRange (Erf[g (c-sMin)]+Erf[g (x-c)])/(Erf[g (c-sMax)]+Erf[g (sMin-c)])],Listable];
linearExtensionFunc=Function[{x},Evaluate[Simplify[x +Floor[disFunc[\[CapitalOmega][[2]]]]- \[CapitalOmega][[2]]-1]]];

If[\[Delta]/K > 1,
\[CapitalOmega]p={0,0};
\[CapitalOmega]p[[2]]=Round[x/.NSolve[linearExtensionFunc[x]==disFunc[x]&&x>= \[CapitalOmega][[2]],x,Reals,WorkingPrecision->1]][[1]];
\[CapitalOmega]p[[1]]=Round[\[CapitalOmega][[1]]]-(\[CapitalOmega]p[[2]]-Round[\[CapitalOmega][[2]]]);
If[Not[\[CapitalOmega]p[[2]]< \[CapitalLambda][[2]]-1], \[CapitalOmega]p[[2]]= \[CapitalLambda][[2]]];
If[Not[\[CapitalOmega]p[[1]]> \[CapitalLambda][[1]]+1], \[CapitalOmega]p[[1]]= \[CapitalLambda][[1]]];
\[Omega]p=pointToUnit[\[CapitalOmega]p,{{sMin,sMax},{sMin,sMax}}];
];
{"\[Mu]" -> \[Mu] , "c" -> c, "\[Sigma]" -> \[Sigma], "s" -> s, "\[Gamma]" -> \[Gamma], "g" -> g,
"sMin"->sMin, "sMax"->sMax, "dMin"->dMin, "dMax"->dMax, "sRange"->sRange, "dRange"->dRange,
"K"->K, "\[Delta]"->\[Delta], "m"->m, "\[Omega]"->\[Omega], "\[CapitalOmega]"->\[CapitalOmega], "\[Omega]p"->\[Omega]p, "\[CapitalOmega]p"->\[CapitalOmega]p, "\[Lambda]"->\[Lambda], "\[CapitalLambda]"->\[CapitalLambda],"dis"->disFunc}
]


Clear[setUpErf,unitGrad]
setUpErf[ \[Sigma]s\[Gamma]g_,\[Mu]c_,{{sMin_,sMax_},{dMin_,dMax_}},opts:OptionsPattern[]]:= Module[{x,\[Mu],c,\[Sigma],s,\[Gamma],g,sRange,dRange,\[Kappa],\[Delta],m,\[Lambda],\[CapitalLambda],\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,linear,shift,dis,sPts,pts,tickstyle},
{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}= setDistroValues[ \[Sigma]s\[Gamma]g,\[Mu]c,{{sMin,sMax},{dMin,dMax}},opts];
{{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],\[CapitalLambda]},{\[Omega],\[CapitalOmega]}}=setDistroParams[ {{\[Mu],c},{\[Sigma],s},{\[Gamma],g}},{{sMin,sMax},{dMin,dMax}}];
dis["vars"]={{\[Mu],c},{\[Sigma],s},{\[Gamma],g}};
dis["ranges"]={{sMin,sMax},{dMin,dMax}};
dis["param"]={{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],\[CapitalLambda]},{\[Omega],\[CapitalOmega]}};
dis["func"]=Function[{x},Evaluate[dMin-dRange (Erf[g (c-sMin)]+Erf[g (x-c)])/(Erf[g (c-sMax)]+Erf[g (sMin-c)])],Listable];
dis["keepQ"]=\[Delta]/\[Kappa] > 1;

dis["linearExtensionFunc"]=Function[{x},Evaluate[Simplify[x +Floor[dis["func"][\[CapitalOmega][[2]]]]- \[CapitalOmega][[2]]-1]]];
If[dis["keepQ"],
\[CapitalOmega]p={0,0};
\[CapitalOmega]p[[2]]=Round[x/.NSolve[dis["linearExtensionFunc"][x]==dis["func"][x]&&x>= \[CapitalOmega] [[2]],x,Reals,WorkingPrecision->1]][[1]];
\[CapitalOmega]p[[1]]=Round[\[CapitalOmega] [[1]]]-(\[CapitalOmega]p[[2]]-Round[\[CapitalOmega] [[2]]]);
dis["redistributeQ"]={\[CapitalOmega]p[[1]]> \[CapitalLambda][[1]]+1,\[CapitalOmega]p[[2]]< \[CapitalLambda][[2]]-1};
If[Not[dis["redistributeQ"][[2]]], \[CapitalOmega]p[[2]]= \[CapitalLambda][[2]]];
If[Not[dis["redistributeQ"][[1]]], \[CapitalOmega]p[[1]]= \[CapitalLambda][[1]]];
\[Omega]p=pointToUnit[\[CapitalOmega]p,{{sMin,sMax},{sMin,sMax}}];
dis["param"]={{sRange,dRange,\[Kappa]},{\[Delta],m},{\[Lambda],\[CapitalLambda]},{\[Omega],\[CapitalOmega]},{\[Omega]p,\[CapitalOmega]p}};
dis["extendedKeepQ"]={\[CapitalOmega]p[[1]]< \[CapitalOmega] [[1]],\[CapitalOmega]p[[2]]> \[CapitalOmega] [[2]]};,
dis["redistributeQ"]={True,True};
dis["extendedKeepQ"]={False,False};
];
dis["disgardQ"]= {Round[\[CapitalLambda][[1]]]>sMin+1,Round[\[CapitalLambda][[2]]]<sMax-1};

dis["selectRegions"]=Function[{list},Evaluate[ReleaseHold@{
If[dis["disgardQ"][[1]],            list[[1]],Hold[Sequence[]]],
If[dis["redistributeQ"][[1]],list[[2]], Hold[Sequence[]]],
If[dis["extendedKeepQ"][[1]],list[[3]],Hold[Sequence[]]],
If[dis["keepQ"],                              list[[4]],Hold[Sequence[]]],
If[dis["extendedKeepQ"][[2]],list[[5]],Hold[Sequence[]]],
If[dis["redistributeQ"][[2]],list[[6]], Hold[Sequence[]]],
If[dis["disgardQ"][[2]],           list[[7]], Hold[Sequence[]]]}
]];

dis["regionNames"]= dis["selectRegions"][
{"Disgard","Redistribute","Extended Keep","Keep","Extended Keep","Redistribute","Disgard"}];
dis["numRegions"]=Length[dis["regionNames"]];

bounds=Table[0,{i,1,dis["numRegions"]+1}];
syms=Table[column[""],{i,1,dis["numRegions"]+1}];
i=1;
syms[[i]]=column["tMin"]; bounds[[i]]=sMin;
If[dis["disgardQ"][[1]],            i++;syms[[i]]=column["\!\(\*SubscriptBox[\(\[CapitalLambda]\), \(1\)]\)"];   bounds[[i]]=N[\[CapitalLambda][[1]]],   AppendTo[syms[[i]],"\!\(\*SubscriptBox[\(\[CapitalLambda]\), \(1\)]\)"] ];
If[dis["redistributeQ"][[1]] ,i++;syms[[i]]=column["\!\(\*SubscriptBox[\(\[CapitalOmega]p\), \(1\)]\)"]; bounds[[i]]=N[\[CapitalOmega]p[[1]]],AppendTo[syms[[i]],"\!\(\*SubscriptBox[\(\[CapitalOmega]p\), \(1\)]\)"]];
If[dis["extendedKeepQ"][[1]],i++;syms[[i]]=column["\!\(\*SubscriptBox[\(\[CapitalOmega]\), \(1\)]\)"];    bounds[[i]]=N[\[CapitalOmega][[1]]],  AppendTo[syms[[i]],"\!\(\*SubscriptBox[\(\[CapitalOmega]\), \(1\)]\)"]];
If[dis["keepQ"],                              i++;syms[[i]]=column["\!\(\*SubscriptBox[\(\[CapitalOmega]\), \(2\)]\)"];    bounds[[i]]=N[\[CapitalOmega][[2]]],  AppendTo[syms[[i]],"\!\(\*SubscriptBox[\(\[CapitalOmega]\), \(2\)]\)"]];
If[dis["extendedKeepQ"][[2]],i++;syms[[i]]=column["\!\(\*SubscriptBox[\(\[CapitalOmega]p\), \(2\)]\)"];  bounds[[i]]=N[\[CapitalOmega]p[[2]]],AppendTo[syms[[i]],"\!\(\*SubscriptBox[\(\[CapitalOmega]p\), \(2\)]\)"]];
If[dis["redistributeQ"][[2]],i++;syms[[i]]=column["\!\(\*SubscriptBox[\(\[CapitalLambda]\), \(2\)]\)"];     bounds[[i]]=N[\[CapitalLambda][[2]]],  AppendTo[syms[[i]],"\!\(\*SubscriptBox[\(\[CapitalLambda]\), \(2\)]\)"]];
If[dis["disgardQ"][[2]],            i++;syms[[i]]=column["tMax"];bounds[[i]]=sMax,             AppendTo[syms[[i]],"tMax"]];
dis["regionSymbols"]={syms//.{column[list__]:> Column[{list}],
"\!\(\*SubscriptBox[\(\[CapitalLambda]\), \(1\)]\)"-> "\!\(\*SubscriptBox[\(\[Lambda]\), \(1\)]\)","\!\(\*SubscriptBox[\(\[CapitalLambda]\), \(2\)]\)"-> "\!\(\*SubscriptBox[\(\[Lambda]\), \(2\)]\)","\!\(\*SubscriptBox[\(\[CapitalOmega]p\), \(1\)]\)"->"\!\(\*SubscriptBox[\(\[Omega]p\), \(1\)]\)","\!\(\*SubscriptBox[\(\[CapitalOmega]p\), \(2\)]\)"->"\!\(\*SubscriptBox[\(\[Omega]p\), \(2\)]\)" ,"\!\(\*SubscriptBox[\(\[CapitalOmega]\), \(1\)]\)"->"\!\(\*SubscriptBox[\(\[Omega]\), \(1\)]\)" ,"\!\(\*SubscriptBox[\(\[CapitalOmega]\), \(2\)]\)"->"\!\(\*SubscriptBox[\(\[Omega]\), \(2\)]\)" ,"tMin"->0,"tMax"-> 1 },syms/.column[list__]:> Column[{list}]};
dis["regionBounds"]=bounds;
tickstyle[pos_,txt_]:={pos,  Style[txt,   Bold,Background->None],{0.03,0.01}} ;
dis["ticks"]={Insert[MapThread[tickstyle,{dis["regionBounds"],dis["regionSymbols"][[1]]}],tickstyle[N[c],"\[Mu]"],Round[dis["numRegions"]/2]+1],
Insert[MapThread[tickstyle ,{dis["regionBounds"],dis["regionSymbols"][[2]]}],tickstyle[N[c],"C"],Round[dis["numRegions"]/2]+1]};

dis["opacity"]=0.6;
If[TrueQ[\[Delta]/\[Kappa] < 1],
dis["piecewise"]=Function[{x},Evaluate[Piecewise[{
    {dMin,                                            x<\[CapitalLambda][[1]]}
,{dis["func"][x],\[CapitalLambda][[1]]<=x<\[CapitalLambda][[2]]}
,{dMax,                       \[CapitalLambda][[2]]<=x }}]],Listable];;
dis["color"]=Function[{x,y},Piecewise[{
    {Opacity[dis["opacity"],Red],                                       x<\[CapitalLambda][[1]]}
,{Opacity[dis["opacity"],Green],  \[CapitalLambda][[1]]<=x<\[CapitalLambda][[2]]}
,{Opacity[dis["opacity"],Red],       \[CapitalLambda][[2]]<=x}}]],
linear= Function[{x},Evaluate[x + dis["func"][ \[CapitalOmega]p[[1]] ] - \[CapitalOmega]p[[1]] ]];
shift=dis["func"][ \[CapitalOmega]p[[2]] ]-linear[\[CapitalOmega]p[[2]]];
dis["piecewise"]=Function[{x},Evaluate[Piecewise[dis["selectRegions"][{
    {dMin,                                                           x<\[CapitalLambda][[1]]}
,{dis["func"][x],               \[CapitalLambda][[1]]<=x<\[CapitalOmega]p[[1]]}
,{linear[x],                         \[CapitalOmega]p[[1]]<=x<\[CapitalOmega][[1]]}
,{linear[x],                           \[CapitalOmega][[1]]<=x<\[CapitalOmega][[2]]}
,{linear[x],                           \[CapitalOmega][[2]]<=x<\[CapitalOmega]p[[2]]}
,{dis["func"][x]-shift,\[CapitalOmega]p[[2]]<=x<\[CapitalLambda][[2]]}
,{dMax -shift,                      \[CapitalLambda][[2]]<=x}}]]],Listable];
dis["color"]=Function[{x,y},Evaluate[Piecewise[dis["selectRegions"][{
    {Opacity[dis["opacity"],Red],                       x<\[CapitalLambda][[1]]}
,{Opacity[dis["opacity"],Green],\[CapitalLambda][[1]]<=x<\[CapitalOmega]p[[1]]}
,{Opacity[dis["opacity"],RGBColor[0.25,0.75,1]],\[CapitalOmega]p[[1]]<=x<\[CapitalOmega][[1]]}
,{Opacity[dis["opacity"],Blue],  \[CapitalOmega][[1]]<=x<\[CapitalOmega][[2]]}
,{Opacity[dis["opacity"],RGBColor[0.25,0.75,1]],\[CapitalOmega][[2]]<=x<\[CapitalOmega]p[[2]]}
,{Opacity[dis["opacity"],Green],\[CapitalOmega]p[[2]]<=x<\[CapitalLambda][[2]]}
,{Opacity[dis["opacity"],Red],     \[CapitalLambda][[2]]<=x}}]]
]]
];
sPts=Sort[Flatten[{\[CapitalOmega],\[CapitalLambda]}]];
dis["pts"]=Transpose[{sPts,dis["func"][sPts]}];
dis
]


Clear[AlternateTicks];
AlternateTicks[ticks_,topQ_:False]:=Module[{out,top,bottom},out=ticks;
If[topQ,  
top="";bottom=Graphics[{Line[{{0,0},{0,0.1}}]}];,
top=Graphics[{Line[{{0,0},{0,0.1}}]}]; bottom="";
];Do[If[OddQ[i],out[[i,2]]=Column[{top,ticks[[i,2]]},Center,0],out[[i,2]]=Column[{ticks[[i,2]],bottom },Center,0]],{i,1,Length[ticks]}];out]


ClearAll[DistroPlot]
TablePos::usage="Table position option for DistroPlot";
NumTicks::usage="Number of ticks to use. Option for DistroPlot";
Options[DistroPlot]={TablePos->{{.05,.95},{0,1}},ImageSize->500,NumTicks->5};
DistroPlot[dist_,OptionsPattern[]]:=Module[{testBg,circSize,plt,usePiecewise},
usePiecewise=dist["piecewise"][dist["ranges"][[1,2]]]<.98dist["ranges"][[2,2]];
testBg=CheckerBoardFromList[dist["regionBounds"], dist["ranges"][[2]],
dist["selectRegions"][{
{Opacity[dist["opacity"],Red]},{Opacity[dist["opacity"],Green]},
{Opacity[dist["opacity"],RGBColor[0.25,0.75,1]]},{Opacity[dist["opacity"],Blue]},{Opacity[dist["opacity"],RGBColor[0.25,0.75,1]]},{Opacity[dist["opacity"],Green]},
{Opacity[dist["opacity"],Red]}}],
Map[List,dist["regionNames"]], {0,-0.6},{0,1},0.8];
circSize={0.02,0.02}( dist["ranges"][[1,2]]- dist["ranges"][[1,1]]);
plt=Plot[Evaluate[If[usePiecewise,{ dist["func"][x], dist["piecewise"][x]},dist["func"][x]]],{x,dist["ranges"][[1,1]],dist["ranges"][[1,2]]},
Frame->True,PlotStyle->{Black,Black},
FrameTicks->{ {BinaryTicks[dist["ranges"][[2,1]],dist["ranges"][[2,2]],3],None},
{MixTicks[Map[{#[[1]],#[[2]]/256}&,BinaryTicks[dist["ranges"][[1,1]],dist["ranges"][[1,2]],OptionValue[NumTicks]]], AlternateTicks[dist["ticks"][[1]],False ],2 OptionValue[NumTicks]],
MixTicks[BinaryTicks[dist["ranges"][[1,1]],dist["ranges"][[1,2]],OptionValue[NumTicks]], AlternateTicks[dist["ticks"][[2]],True ],2 OptionValue[NumTicks]] }},
Epilog->{
LabelPointGrad[ dist["vars"] [[1,2]], dist["func"][#1] &,Round[ dist["vars"] [[1,2]]],Blue,{0,0},11,circSize ],
LabelPointGrad[ dist["param"] [[4,2,1]], dist["func"][#1] &,Round[ dist["param"] [[4,2,1]]],Green,{0,0},11,circSize ],
LabelPointGrad[ dist["param"] [[4,2,2]], dist["func"][#1] &,Round[ dist["param"] [[4,2,2]]],Green,{0,0},11,circSize ],
LabelPoint[ dist["param"] [[3,2,1]], dist["func"][#1] &,Round[ dist["param"] [[3,2,1]]],Red,{0,0},circSize ],
LabelPoint[ dist["param"] [[3,2,2]], dist["func"][#1] &,Round[ dist["param"] [[3,2,2]]],Red,{0,0},circSize ],
Inset[Panel[valTable[ dist["vars"], dist["ranges"]],Background->Opacity[0.5,White]],Scaled[OptionValue[TablePos][[1]]],Scaled[OptionValue[TablePos][[2]]]],
Text[If[usePiecewise,"Compact Distribution",""],{ dist["ranges"][[1,2]], dist["piecewise"][ dist["ranges"][[1,2]]]},{1,1}],
Text["Full Range Distribution",{ dist["ranges"][[1,2]], dist["func"][ dist["ranges"][[1,2]]]},{1,1}]},AspectRatio->1,ImageSize->OptionValue[ImageSize]];
Show[plt,Graphics[{Opacity[0.15],testBg}],plt]
]


(* ::Subsection:: *)
(*Distributions with Rotations Parameters*)


Format[\[Lambda]RGB2, TraditionalForm]= Subsuperscript[Style["\[Lambda]",Bold],"2","RGB"];
\[Lambda]RGB2[\[Theta]_,\[Lambda]:{_,_,_}]:=Module[{correctToRGBCube,\[Lambda]CubeRGB},
correctToRGBCube[pnt_]:=Block[{mm},mm={Min[pnt],Max[pnt]};
If[mm[[1]]<0,pnt-mm[[1]],If[mm[[2]]>1,pnt-(mm[[2]]-1)]]
];
\[Lambda]CubeRGB=(inLCaCb[\[Theta]].(cubeCorners[\[Lambda]]-{0,0.5,0.5}));
\[Lambda]CubeRGB=Transpose[Table[correctToRGBCube[\[Lambda]CubeRGB[[All,i]]],{i,1,Length[\[Lambda]CubeRGB[[1]]]}]];
Map[Max,\[Lambda]CubeRGB]
];



Clear[colorSpaceParams]
colorSpaceParams::usage = 
  "Input 3 distributions from setUpErf and a color space angle to get:\n
 {\"\[Delta]qS\",\"L\",\"sRange\",\"dRange\",\"K\",\"\[Delta]\",\"\[Lambda]\",\"\[Omega]\",\"\[Omega]p\",\"\[Kappa]\",\"tRange\",\"\[Lambda]RGB2\",\"mp\",\"\[Alpha]\[Beta]\",\"\[Alpha]\",\"\[Beta]\",\"\[Tau]\",\"axisColors\"}";
colorSpaceParams[\[Sigma]s\[Gamma]g_,\[Mu]c_,\[Theta]in_,n_,{{sMin_,sMax_},{dMin_,dMax_}},opts:OptionsPattern[]]:=Module[{varRules,
\[Theta],\[Delta]qSval,L,sRange,dRange,K,\[Delta],m,\[Lambda],\[CapitalLambda],\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,\[Kappa],tRange,\[Lambda]RGB2val,mp,\[Alpha]\[Beta],\[Alpha],\[Beta],\[Tau],LCaCbColor,qRsMin,qRsMax,qRsRange,\[CapitalLambda]t,\[CapitalOmega]pt,\[CapitalLambda]q,\[CapitalOmega]pq,Qdisc,Qdist,Qkeep,
S,disFun,disFunc,dstMax,\[Mu],c,\[Sigma],s,\[Gamma],g,distro,qRval,fSsVal},
(* Put the distribution parameters together into vectors *)
distro=Table[DistroAll[\[Sigma]s\[Gamma]g[[i]],\[Mu]c[[i]],{{sMin[[i]],sMax[[i]]},{dMin[[i]],dMax[[i]]}},opts] ,{i,1,3}];
{\[Mu],c,\[Sigma],s,\[Gamma],g}=Transpose[{"\[Mu]","c","\[Sigma]","s","\[Gamma]","g"}/.distro];
{sRange,dRange}=Transpose[{"sRange","dRange"}/.distro];
{K,\[Delta],m,\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,\[Lambda],\[CapitalLambda],disFunc}=Transpose[{"K","\[Delta]","m","\[Omega]","\[CapitalOmega]","\[Omega]p","\[CapitalOmega]p","\[Lambda]","\[CapitalLambda]","dis"}/.distro];

\[Delta]qSval=Global`\[Delta]qS[\[Theta]in];
L=scale["LCaCb","nLCaCb"][\[Theta]in];
\[Kappa]=MapThread[Max,{(1/\[Delta]),K/L}];
tRange=MapThread[Min,{(K \[Delta]),L}];
\[Lambda]RGB2val=Global`\[Lambda]RGB2[\[Theta]in,\[Lambda]];
mp=Map[Max,Transpose[Transpose[\[Delta]qSval] \[Lambda]RGB2val]];
\[Alpha]\[Beta]=\[Delta]qEO[2 (tRange) (mp), \[Theta]in];
\[Alpha] = \[Alpha]\[Beta][[2]]; \[Beta] = \[Alpha]\[Beta][[3]];
\[Tau]=Block[{accuracy},accuracy=0.01;Rationalize[accuracy Ceiling[1/(accuracy Max[\[Alpha]\[Beta]])],accuracy]];
SetUpLCaCbColor[SymbolName[LCaCbColor],-\[Theta]in,"Hue"];

qRsMin={0,- 2^(n-2) (2^n-1),- 2^(n-2) (2^n-1)};
qRsMax={0, 2^(n-2) (2^n-1),2^(n-2) (2^n-1)};
qRsRange={3 2^n,2 2^(n-2) (2^n-1),2 2^(n-2) (2^n-1)};
\[CapitalLambda]t  = Round[(dRange tRange) \[Lambda]];
\[CapitalOmega]pt = Round[(dRange tRange) \[Omega]p];
\[CapitalLambda]q  = Round[(qRsRange) \[Lambda]];
\[CapitalOmega]pq = Round[qRsRange \[Omega]p];

Qdisc = Map[(2^3/2^n<#)&,({1,1,1}-\[Lambda][[All,2]]+\[Lambda][[All,1]])];
Qdist = Map[(2^3/2^n<#)&,(\[Lambda][[All,2]]-\[Omega]p[[All,2]]+\[Omega]p[[All,1]]-\[Lambda][[All,1]])];
Qkeep = Map[(1/2^n<#)&,(\[Omega]p[[All,2]]-\[Omega]p[[All,1]])];
S = MapThread[Min,{\[Delta] K,N[L]}] {1/3,2^(1-n),2^(1-n)};

disFun = Table[
func = Function[{x}, Evaluate[dis[x, qRsRange[[i]] \[Sigma][[i]], qRsRange[[i]] \[Mu][[i]], 0, qRsRange[[i]], dMin[[i]], dMax[[i]]] ]]; 
Function[{x}, Evaluate[
If[Qkeep[[i]] && Qdisc[[i]] && Qdist[[i]], 
  Piecewise[{
   {dMin[[i]],                                                                              x <= \[CapitalLambda]q[[i,1]]}, 
   {func[x],                                                            \[CapitalLambda]q[[i,1]] <  x <  \[CapitalOmega]pq[[i,1]]}, 
   {S[[i]]*x - S[[i]]*\[CapitalOmega]pq[[i,1]] + func[\[CapitalOmega]pq[[i,1]]],                               \[CapitalOmega]pq[[i,1]] <= x <= \[CapitalOmega]pq[[i,2]]}, 
   {func[x] + S[[i]]*\[CapitalOmega]pq[[i,2]] - S[[i]]*\[CapitalOmega]pq[[i,1]] - func[\[CapitalOmega]pq[[i,2]]] + func[\[CapitalOmega]pq[[i,1]]], \[CapitalOmega]pq[[i,2]] <  x < \[CapitalLambda]q[[i,2]]}, 
   {func[\[CapitalLambda]q[[i,2]]] + S[[i]]*\[CapitalOmega]pq[[i,2]] - S[[i]]*\[CapitalOmega]pq[[i,1]] - func[\[CapitalOmega]pq[[i,2]]] + func[\[CapitalOmega]pq[[i,1]]],  \[CapitalLambda]q[[i,2]] <= x}}], 
If[Qkeep[[i]] && Qdisc[[i]] &&  !Qdist[[i]], 
Piecewise[{
{dMin[[i]], x <= \[CapitalLambda]q[[i,1]]}, 
{S[[i]]*(x - \[CapitalLambda]q[[i,1]]) + dMin[[i]], \[CapitalLambda]q[[i,1]] < x < \[CapitalLambda]q[[i,2]]}, 
{S[[i]]*(\[CapitalLambda]q[[i,2]] - \[CapitalLambda]q[[i,1]]) + dMin[[i]], \[CapitalLambda]q[[i,2]] <= x}}], 
If[Qkeep[[i]] &&  !Qdisc[[i]] &&  !Qdist[[i]], 
S[[i]]*x + dMin[[i]], 
If[ !Qkeep[[i]] && Qdisc[[i]] && Qdist[[i]], Piecewise[{
{dMin[[i]], x <= \[CapitalLambda]q[[i,1]]}, 
{func[S[[i]]*x], \[CapitalLambda]q[[i,1]] < x < \[CapitalLambda]q[[i,2]]}, {dMax[[i]], \[CapitalLambda]q[[i,2]] <= x}}], 
If[ Qkeep[[i]] && !Qdisc[[i]] && Qdist[[i]], 
  Piecewise[{
   {func[x],                                                                         x <  \[CapitalOmega]pq[[i,1]]}, 
   {S[[i]]*(x - \[CapitalOmega]pq[[i,1]]) + func[\[CapitalOmega]pq[[i,1]]],                                    \[CapitalOmega]pq[[i,1]] <= x <= \[CapitalOmega]pq[[i,2]]}, 
   {func[x] + \[CapitalOmega]p[[i,2]] - \[CapitalOmega]p[[i,1]] - func[\[CapitalOmega]pq[[i,2]]] + func[\[CapitalOmega]pq[[i,1]]], \[CapitalOmega]pq[[i,2]] <  x }
  }], 
If[ !Qkeep[[i]] && Qdisc[[i]] &&  !Qdist[[i]], Piecewise[{
{dMin[[i]], x <= (1/2)*(\[CapitalLambda]q[[i,1]] + \[CapitalLambda]q[[i,1]])}, 
{dMin[[i]] + 1, (1/2)*(\[CapitalLambda]q[[i,1]] + \[CapitalLambda]q[[i,1]]) < x}}], 
If[ !Qkeep[[i]] &&  !Qdisc[[i]] &&  !Qdist[[i]], 
              Message[error]]]]]]]]]], {i, 1, 3}];

dstMax = Table[Round[disFun[[i]][qRsRange[[i]]]],{i,1,3}];

qRval = Global`qR[\[Theta]in];

fSsVal = Global`fSs[\[Theta]in];

{"\[Mu]" -> \[Mu] , "c" -> c, "\[Sigma]" -> \[Sigma], "s" -> s, "\[Gamma]" -> \[Gamma], "g" -> g,
"sMin"->sMin, "sMax"->sMax, "dMin"->dMin, "dMax"->dMax, "sRange"->sRange, "dRange"->dRange,
"K"->K, "\[Delta]"->\[Delta], "m"->m, "\[Omega]"->\[Omega], "\[CapitalOmega]"->\[CapitalOmega], "\[Omega]p"->\[Omega]p, "\[CapitalOmega]p"->\[CapitalOmega]p, "\[Lambda]"->\[Lambda], "\[CapitalLambda]"->\[CapitalLambda],"dis"->disFunc,
"\[Theta]"->\[Theta]in,"\[Delta]qS"->\[Delta]qSval,"L"->(L),"\[Kappa]"->\[Kappa],"tRange"->tRange,"\[Lambda]RGB2"->\[Lambda]RGB2val,"mp"->mp,"\[Alpha]\[Beta]"->\[Alpha]\[Beta],"\[Alpha]"->\[Alpha],"\[Beta]"->\[Beta],"\[Tau]"->\[Tau],"LCaCbColor"->LCaCbColor,
"qRsMin"->qRsMin, "qRsMax"->qRsMax, "qRsRange"->qRsRange, "\[CapitalLambda]t"->\[CapitalLambda]t,"\[CapitalOmega]pt"->\[CapitalOmega]pt,"\[CapitalLambda]q"->\[CapitalLambda]q,"\[CapitalOmega]pq"->\[CapitalOmega]pq,"Qdisc"->Qdisc,"Qdist"->Qdist,"Qkeep"->Qkeep,"S"->S,
"disFun"->disFun,"dstMax"->dstMax,"qR"->qRval,"fSs"->fSsVal}
]

setColorSpaceParams[\[Sigma]s\[Gamma]g_,\[Mu]c_,\[Theta]in_,n_,sdMinMax:{{_,_},{_,_}},opts:OptionsPattern[]]:=Module[{rules},
Clear[sMin,sMax,dMin,dMax,sRange,dRange,
K,\[Delta],m,\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,\[Lambda],\[CapitalLambda],dis,\[Theta],\[Delta]qSval,L,\[Kappa],tRange,\[Lambda]RGB2val,mp,\[Alpha]\[Beta],\[Alpha],\[Beta],\[Tau],
LCaCbColor,qRsMin,qRsMax,qRsRange,\[CapitalLambda]q,\[CapitalOmega]pq,
Qdisc,Qdist,Qkeep,S,disFun,dstMax,qRval,fSsVal] ;

rules=colorSpaceParams[\[Sigma]s\[Gamma]g,\[Mu]c,\[Theta]in,n,sdMinMax,opts];

{\[Mu],c,\[Sigma],s,\[Gamma],g,sMin,sMax,dMin,dMax,sRange,dRange,
K,\[Delta],m,\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,\[Lambda],\[CapitalLambda],disFunc,\[Theta],\[Delta]qSval,L,\[Kappa],tRange,\[Lambda]RGB2val,mp,\[Alpha]\[Beta],\[Alpha],\[Beta],\[Tau],
LCaCbColor,qRsMin,qRsMax,qRsRange,\[CapitalLambda]q,\[CapitalOmega]pq,
Qdisc,Qdist,Qkeep,S,disFun,dstMax,qRval,fSsVal}=
{"\[Mu]","c","\[Sigma]","s","\[Gamma]","g","sMin","sMax","dMin","dMax","sRange","dRange",
"K","\[Delta]","m","\[Omega]","\[CapitalOmega]","\[Omega]p","\[CapitalOmega]p","\[Lambda]","\[CapitalLambda]","dis",
"\[Theta]","\[Delta]qS","L","\[Kappa]","tRange","\[Lambda]RGB2","mp","\[Alpha]\[Beta]","\[Alpha]","\[Beta]","\[Tau]",
"LCaCbColor","qRsMin","qRsMax","qRsRange","\[CapitalLambda]q","\[CapitalOmega]pq",
"Qdisc","Qdist","Qkeep","S","disFun","dstMax","qR","fSs"}/.rules
]


Clear[\[Mu],c,\[Sigma],s,\[Gamma],g,sMin,sMax,dMin,dMax,sRange,dRange,K,\[Delta],m,\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,\[Lambda],\[CapitalLambda],\[Theta],\[Delta]qSval,L,\[Kappa],tRange,\[Lambda]RGB2val,mp,\[Alpha]\[Beta],\[Alpha],\[Beta],\[Tau],
 LCaCbColor,qRsMin,qRsMax,qRsRange,\[CapitalLambda]q,\[CapitalOmega]pq,Qdisc,Qdist,Qkeep,S,disFun,dstMax,qRval,fSsVal]


Clear[processImage];
processImage[imgData_, qFuns_:{},dFuns_:{}, \[Sigma]s\[Gamma]g_, \[Mu]c_, \[Theta]in_, n_, sdMinMax:{{_,_},{_,_}}, opts:OptionsPattern[]]:=Module[ {rules},
rules=colorSpaceParams[\[Sigma]s\[Gamma]g,\[Mu]c,\[Theta]in,n,sdMinMax,opts];
processImage[imgData, qFuns,dFuns, rules, opts]
]

processImage[imgData_, qFuns_:{},dFuns_:{}, rules_List, opts:OptionsPattern[]]:=Module[
{sMin,sMax,dMin,dMax,sRange,dRange,
K,\[Delta],m,\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,\[Lambda],\[CapitalLambda],dis,\[Theta],\[Delta]qSval,L,\[Kappa],tRange,\[Lambda]RGB2val,mp,\[Alpha]\[Beta],\[Alpha],\[Beta],\[Tau],
LCaCbColor,qRsMin,qRsMax,qRsRange,\[CapitalLambda]q,\[CapitalOmega]pq,Qdisc,Qdist,Qkeep,S,disFun,dstMax,qRval,fSsVal,pxl,qPxl,dqPxl},
{\[Mu],c,\[Sigma],s,\[Gamma],g,sMin,sMax,dMin,dMax,sRange,dRange,
K,\[Delta],m,\[Omega],\[CapitalOmega],\[Omega]p,\[CapitalOmega]p,\[Lambda],\[CapitalLambda],dis,\[Theta],\[Delta]qSval,L,\[Kappa],tRange,\[Lambda]RGB2val,mp,\[Alpha]\[Beta],\[Alpha],\[Beta],\[Tau],
LCaCbColor,qRsMin,qRsMax,qRsRange,\[CapitalLambda]q,\[CapitalOmega]pq,
Qdisc,Qdist,Qkeep,S,disFun,dstMax,qRval,fSsVal}=
{"\[Mu]","c","\[Sigma]","s","\[Gamma]","g","sMin","sMax","dMin","dMax","sRange","dRange",
"K","\[Delta]","m","\[Omega]","\[CapitalOmega]","\[Omega]p","\[CapitalOmega]p","\[Lambda]","\[CapitalLambda]","dis",
"\[Theta]","\[Delta]qS","L","\[Kappa]","tRange","\[Lambda]RGB2","mp","\[Alpha]\[Beta]","\[Alpha]","\[Beta]","\[Tau]",
"LCaCbColor","qRsMin","qRsMax","qRsRange","\[CapitalLambda]q","\[CapitalOmega]pq",
"Qdisc","Qdist","Qkeep","S","disFun","dstMax","qR","fSs"}/.rules;
Table[
pxl=imgData[[i,j]];
qPxl=fSsVal (qRval.pxl) -qRsMin;
dqPxl=Table[N[Round[disFun[[i]] [qPxl[[i]]]]/dstMax[[i]]],{i,1,3}];
Do[
AppendTo[dqPxl, qFuns[[i]][qPxl]];
,{i,1,Length[qFuns]}];
Do[
AppendTo[dqPxl, dFuns[[i]][dqPxl]];
,{i,1,Length[dFuns]}];
dqPxl
,{i,1,(Dimensions[imgData])[[1]]},{j,1,(Dimensions[imgData])[[2]]}]
]


ClearAll[paramTable]
Digits::usage="Option for paramTable. NumberForm specification for {Integers, Decimals}";
Options[paramTable]={Digits->{{4,0},{5,3}}};
paramTable[dist_,OptionsPattern[]]:=Module[{},Block[{\[Mu],c,\[Sigma],s,\[Gamma],g,sMin,sMax,sRange,dMin,dMax,dRange,s\[CapitalDelta],d\[CapitalDelta],\[Kappa],\[Delta],m,\[Omega],\[CapitalOmega],\[Lambda],L},
{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=dist["vars"];{{sMin,sMax},{dMin,dMax}}=dist["ranges"];
paramNames={{"sRange","dRange","K"},{"\[Delta]","m"},{"\[Lambda]","\[CapitalLambda]"},{"\[Omega]","\[CapitalOmega]"},{"\[Omega]p","\[CapitalOmega]p"}};
srcForm=NumberForm[#,(OptionValue[Digits][[1]]),NumberPoint->""]&;
unitForm=NumberForm[N[#],OptionValue[Digits][[2]],NumberPadding->{" ", "0"}]&;
numForm={{srcForm,srcForm,unitForm},{unitForm,srcForm},{unitForm,srcForm},{unitForm,srcForm},{unitForm,srcForm}};
paramVals=dist["param"];
dispElem=Table[Table[Row[{paramNames[[i,j]]," = ",numForm[[i,j]][MatrixForm[paramVals[[i,j]]]]}],{j,1,Length[paramNames[[i]]]}]
,{i,1,Length[paramNames]}];
Column[{
Grid[{{dispElem[[1,2]],dispElem[[1,3]]},{dispElem[[1,1]],SpanFromAbove}},Alignment->{Center,Center},Frame->All],
Grid[{{"",Column[{"Unit","0-1"},Alignment->Center],Column[{"Src",ToString[sMin]<>" - "<>ToString[sMax]},Alignment->Center]},
{"Mean", Row[{"\[Mu] = ",unitForm[\[Mu]]}],Row[{"c = ",srcForm[c]}]},
{"Std",  Row[{"\[Sigma] = ",unitForm[\[Sigma]]}],Row[{"s = ",NumberForm[s,4]}]},
{"G",    Row[{"\[Gamma] = ",unitForm[\[Gamma]]}],Row[{"g = ",NumberForm[g,{4,4}]}]},
{"Gradient",dispElem[[2,1]],dispElem[[2,2]]},
{"Discard All",dispElem[[3,1]],dispElem[[3,2]]},
{"Keep All",dispElem[[4,1]],dispElem[[4,2]]},
{"Extended Keep",dispElem[[5,1]],dispElem[[5,2]]}},Alignment->{Center,Center},Frame->All]}]]];


colorSpaceParamElems[dist_,\[Theta]in_]:=Module[{distRules,calcNotes,notes,bright,sat,channelNames,channelColors,AxisColorStrips,paramTables,valTables,dispRules,tol,pbPlot,pb\[Tau]Plot},
distRules=colorSpaceParams[dist,\[Theta]in];
(* Notes *)
calcNotes={};
Do[
AppendTo[calcNotes,ReleaseHold[TraditionalForm[Hold[Row[{\[Kappa]["\[Theta]'"]," = ","Max"[1/"\[Delta]"[[i]],"K"[[i]]/"L"[[i]] ]," = ","\[Kappa]"[[i]]}]]/.distRules]]];
AppendTo[calcNotes,ReleaseHold[TraditionalForm[Hold[Row[{tRange["\[Theta]',\[Mu]',\[Sigma]"]," = ","Min"["K"[[i]] "\[Delta]"[[i]],"L"[[i]] ]," = ","tRange"[[i]]}]]/.distRules]]];
,{i,1,3}];
AppendTo[calcNotes,TraditionalForm[Row[{"Max["\[Delta]qS["\[Theta]'"],"\[CircleTimes]",\[Lambda]RGB2["\[Theta]'","\[Lambda]"],"] = ","Max"[Transpose[Transpose[\[Delta]qSVal] \[Lambda]RGB2[\[Theta]p,\[Lambda]Val]]]," = ",MatrixForm[Map[Max,Transpose[Transpose[\[Delta]qSVal] \[Lambda]RGB2[\[Theta]p,\[Lambda]Val]]]]}]]];
AppendTo[calcNotes,TraditionalForm[Row[{MatrixForm[{0,"\[Alpha]","\[Beta]"}]," = ",2 \[Delta]qEO ["Min"["K" "\[Delta]", "L"] "Max"[\[Delta]qS["\[Theta]'"],"\[CircleTimes]",\[Lambda]RGB2["\[Theta]'","\[Lambda]"]]]," = ",MatrixForm[{null,"\[Alpha]"/.distRules,"\[Beta]"/.distRules}]}]]];
AppendTo[calcNotes,TraditionalForm[Row[{\[Tau]," = ","Max[\[Alpha], \[Beta]]"^-1," \[TildeEqual] ","\[Tau]"/.distRules}]]];
notes=Panel[Grid[{{Column[calcNotes[[1;;5;;2]]], Column[calcNotes[[2;;6;;2]]]}, {Column[calcNotes[[7;;]]],SpanFromLeft}},Background->LightYellow,Frame->All],"Calculation Notes"];
(* Axis Colors *)
bright={0.3,0.8}; sat={0.4,0.6};
channelNames={"L ","Ca'","Cb'"};
channelColors={
{"LCaCbColor"[sat[[1]], 0.5, 0.5],         "LCaCbColor"[sat[[2]],0.5,0.5]},
{"LCaCbColor"[bright[[2]],sat[[1]],0.5],   "LCaCbColor"[bright[[2]],sat[[2]],0.5]},
{"LCaCbColor"[bright[[2]], 0.5, sat[[1]]], "LCaCbColor"[bright[[2]],0.5,sat[[2]]]} }/.distRules;
AxisColorStrips=Block[{},
Panel[Column[{
Graphics[Append[Table[{"LCaCbColor"[i,0.5,0.5],Rectangle[{255 i,0},{255 i+1,16}]},{i,0,1,1/255}],Text["L ",{0,16},{-1,-1}]]],
Graphics[Append[Table[{"LCaCbColor"[0.8,i,0.5],Rectangle[{255 i,0},{255 i+1,16}]},{i,0,1,1/255}],Text["Ca'",{0,16},{-1,-1}]]],
Graphics[Append[Table[{"LCaCbColor"[0.8,0.5,i],Rectangle[{255 i,0},{255 i+1,16}]},{i,0,1,1/255}],Text["Cb'",{0,16},{-1,-1}]]]
}]/.distRules]
];
(* Param Tables *)
paramTables=Table[Panel[Panel[paramTable[dist[[i]]],channelNames[[i]],Background->channelColors[[i,2]]],Background->channelColors[[i,1]]],{i,1,3}];
valTables=Table[Panel[Panel[valTable[dist[[i]]["vars"],{{0,255},{0,255}}],channelNames[[i]],Background->channelColors[[i,2]]],Background->channelColors[[i,1]]],{i,1,3}];
(* Display Elements *)
numFrm=(NumberForm[#,4])&;
dispRules={"AxisColorStrips"->AxisColorStrips};
AppendTo[dispRules,"\[Delta]qS"->TraditionalForm[Row[{\[Delta]qS["\[Theta]'"]," = ","\[Delta]qS"/.distRules}]]];
AppendTo[dispRules,"L"->TraditionalForm[Row[{scale["LCaCb","nLCaCb"]["\[Theta]'"]," = ",MatrixForm@("L"/.distRules)}]]];
AppendTo[dispRules,"\[Delta]qEO"->TraditionalForm[Row[{\[Delta]qEO[MatrixForm@{0,a,b},"\[Theta]'"]," = ",MatrixForm@\[Delta]qEO[{0,a,b},"\[Theta]"/.distRules]}]]];
AppendTo[dispRules,"\[Kappa]"->Row[{\[Kappa]["\[Theta]'"]," = ",MatrixForm[("\[Kappa]"/.distRules)]}]];
AppendTo[dispRules,"tRange"->Row[{"tRange = ",MatrixForm[("tRange"/.distRules)]}]];
AppendTo[dispRules,"\[Lambda]RGB2"->TraditionalForm[Row[{\[Lambda]RGB2," = ",MatrixForm[(\[Lambda]RGB2["\[Theta]"/.distRules,"\[Lambda]"/.distRules])]}]]];
AppendTo[dispRules,"\[Alpha]\[Beta]"->TraditionalForm[Row[{MatrixForm[{0,\[Alpha],\[Beta]}]," = ",MatrixForm[{null,"\[Alpha]"/.distRules,"\[Beta]"/.distRules}]}]]];
AppendTo[dispRules,"\[Tau]"->TraditionalForm[Row[{\[Tau]," = ","Max[\[Alpha], \[Beta]]"^-1," \[TildeEqual] ","\[Tau]"/.distRules}]]];
(* Plot Elements *)
pbPlot=perturbationPlot[\[Theta]in,1,8,{"\[Alpha]"/.distRules,"\[Beta]"/.distRules},PlotRange->{Mod[\[Theta]p,Pi/6]-(Pi/84),Mod[\[Theta]p,Pi/6] + (Pi/84)}];
tol=Block[{accuracy},accuracy=0.01;Rationalize[accuracy Ceiling[1/(accuracy Max[{"\[Alpha]"/.distRules,"\[Beta]"/.distRules}])],accuracy]];
pb\[Tau]Plot=perturbationPlot[\[Theta]in,"\[Tau]"/.distRules,8,PlotRange->{Mod[\[Theta]p,Pi/6]-(Pi/84),Mod[\[Theta]p,Pi/6] + (Pi/84)}];

{valTables,paramTables,{(List@@pbPlot)[[1,1,1]],(List@@pbPlot)[[1,1,2,1]]},{(List@@pb\[Tau]Plot)[[1,1,1]],(List@@pb\[Tau]Plot)[[1,1,2,1]]},Grid[{{"AxisColorStrips",SpanFromLeft},{"L","\[Tau]"},{"\[Delta]qS","\[Delta]qEO"},{"\[Kappa]","tRange"},{"\[Lambda]RGB2","\[Alpha]\[Beta]"}},Frame->All]/.dispRules,
notes}
]






(* ::Subsection:: *)
(*Distributions with Rotations Output Tables*)


Format[\[Lambda]RGB2, TraditionalForm]= Subsuperscript[Style["\[Lambda]",Bold],"2","RGB"];
\[Lambda]RGB2[\[Theta]_,\[Lambda]:{_,_,_}]:=Module[{correctToRGBCube,\[Lambda]CubeRGB},
correctToRGBCube[pnt_]:=Block[{mm},mm={Min[pnt],Max[pnt]};
If[mm[[1]]<0,pnt-mm[[1]],If[mm[[2]]>1,pnt-(mm[[2]]-1)]]
];
\[Lambda]CubeRGB=(inLCaCb[\[Theta]].(cubeCorners[\[Lambda]]-{0,0.5,0.5}));
\[Lambda]CubeRGB=Transpose[Table[correctToRGBCube[\[Lambda]CubeRGB[[All,i]]],{i,1,Length[\[Lambda]CubeRGB[[1]]]}]];
Map[Max,\[Lambda]CubeRGB]
];


ClearAll[paramTable]
Digits::usage="Option for paramTable. NumberForm specification for {Integers, Decimals}";
Options[paramTable]={Digits->{{4,0},{5,3}}};
paramTable[dist_,OptionsPattern[]]:=Module[{},Block[{\[Mu],c,\[Sigma],s,\[Gamma],g,sMin,sMax,sRange,dMin,dMax,dRange,s\[CapitalDelta],d\[CapitalDelta],\[Kappa],\[Delta],m,\[Omega],\[CapitalOmega],\[Lambda],L},
{{\[Mu],c},{\[Sigma],s},{\[Gamma],g}}=dist["vars"];{{sMin,sMax},{dMin,dMax}}=dist["ranges"];
paramNames={{"sRange","dRange","K"},{"\[Delta]","m"},{"\[Lambda]","\[CapitalLambda]"},{"\[Omega]","\[CapitalOmega]"},{"\[Omega]p","\[CapitalOmega]p"}};
srcForm=NumberForm[#,(OptionValue[Digits][[1]]),NumberPoint->""]&;
unitForm=NumberForm[N[#],OptionValue[Digits][[2]],NumberPadding->{" ", "0"}]&;
numForm={{srcForm,srcForm,unitForm},{unitForm,srcForm},{unitForm,srcForm},{unitForm,srcForm},{unitForm,srcForm}};
paramVals=dist["param"];
dispElem=Table[Table[Row[{paramNames[[i,j]]," = ",numForm[[i,j]][MatrixForm[paramVals[[i,j]]]]}],{j,1,Length[paramNames[[i]]]}]
,{i,1,Length[paramNames]}];
Column[{
Grid[{{dispElem[[1,2]],dispElem[[1,3]]},{dispElem[[1,1]],SpanFromAbove}},Alignment->{Center,Center},Frame->All],
Grid[{{"",Column[{"Unit","0-1"},Alignment->Center],Column[{"Src",ToString[sMin]<>" - "<>ToString[sMax]},Alignment->Center]},
{"Mean", Row[{"\[Mu] = ",unitForm[\[Mu]]}],Row[{"c = ",srcForm[c]}]},
{"Std",  Row[{"\[Sigma] = ",unitForm[\[Sigma]]}],Row[{"s = ",NumberForm[s,4]}]},
{"G",    Row[{"\[Gamma] = ",unitForm[\[Gamma]]}],Row[{"g = ",NumberForm[g,{4,4}]}]},
{"Gradient",dispElem[[2,1]],dispElem[[2,2]]},
{"Discard All",dispElem[[3,1]],dispElem[[3,2]]},
{"Keep All",dispElem[[4,1]],dispElem[[4,2]]},
{"Extended Keep",dispElem[[5,1]],dispElem[[5,2]]}},Alignment->{Center,Center},Frame->All]}]]];


colorSpaceParamElems[dist_,\[Theta]in_]:=Module[{distRules,calcNotes,notes,bright,sat,channelNames,channelColors,AxisColorStrips,paramTables,valTables,dispRules,tol,pbPlot,pb\[Tau]Plot},
distRules=colorSpaceParams[dist,\[Theta]in];
(* Notes *)
calcNotes={};
Do[
AppendTo[calcNotes,ReleaseHold[TraditionalForm[Hold[Row[{\[Kappa]["\[Theta]'"]," = ","Max"[1/"\[Delta]"[[i]],"K"[[i]]/"L"[[i]] ]," = ","\[Kappa]"[[i]]}]]/.distRules]]];
AppendTo[calcNotes,ReleaseHold[TraditionalForm[Hold[Row[{tRange["\[Theta]',\[Mu]',\[Sigma]"]," = ","Min"["K"[[i]] "\[Delta]"[[i]],"L"[[i]] ]," = ","tRange"[[i]]}]]/.distRules]]];
,{i,1,3}];
AppendTo[calcNotes,TraditionalForm[Row[{"Max["\[Delta]qS["\[Theta]'"],"\[CircleTimes]",\[Lambda]RGB2["\[Theta]'","\[Lambda]"],"] = ","Max"[Transpose[Transpose[\[Delta]qSVal] \[Lambda]RGB2[\[Theta]p,\[Lambda]Val]]]," = ",MatrixForm[Map[Max,Transpose[Transpose[\[Delta]qSVal] \[Lambda]RGB2[\[Theta]p,\[Lambda]Val]]]]}]]];
AppendTo[calcNotes,TraditionalForm[Row[{MatrixForm[{0,"\[Alpha]","\[Beta]"}]," = ",2 \[Delta]qEO ["Min"["K" "\[Delta]", "L"] "Max"[\[Delta]qS["\[Theta]'"],"\[CircleTimes]",\[Lambda]RGB2["\[Theta]'","\[Lambda]"]]]," = ",MatrixForm[{null,"\[Alpha]"/.distRules,"\[Beta]"/.distRules}]}]]];
AppendTo[calcNotes,TraditionalForm[Row[{\[Tau]," = ","Max[\[Alpha], \[Beta]]"^-1," \[TildeEqual] ","\[Tau]"/.distRules}]]];
notes=Panel[Grid[{{Column[calcNotes[[1;;5;;2]]], Column[calcNotes[[2;;6;;2]]]}, {Column[calcNotes[[7;;]]],SpanFromLeft}},Background->LightYellow,Frame->All],"Calculation Notes"];
(* Axis Colors *)
bright={0.3,0.8}; sat={0.4,0.6};
channelNames={"L ","Ca'","Cb'"};
channelColors={
{"LCaCbColor"[sat[[1]], 0.5, 0.5],         "LCaCbColor"[sat[[2]],0.5,0.5]},
{"LCaCbColor"[bright[[2]],sat[[1]],0.5],   "LCaCbColor"[bright[[2]],sat[[2]],0.5]},
{"LCaCbColor"[bright[[2]], 0.5, sat[[1]]], "LCaCbColor"[bright[[2]],0.5,sat[[2]]]} }/.distRules;
AxisColorStrips=Block[{},
Panel[Column[{
Graphics[Append[Table[{"LCaCbColor"[i,0.5,0.5],Rectangle[{255 i,0},{255 i+1,16}]},{i,0,1,1/255}],Text["L ",{0,16},{-1,-1}]]],
Graphics[Append[Table[{"LCaCbColor"[0.8,i,0.5],Rectangle[{255 i,0},{255 i+1,16}]},{i,0,1,1/255}],Text["Ca'",{0,16},{-1,-1}]]],
Graphics[Append[Table[{"LCaCbColor"[0.8,0.5,i],Rectangle[{255 i,0},{255 i+1,16}]},{i,0,1,1/255}],Text["Cb'",{0,16},{-1,-1}]]]
}]/.distRules]
];
(* Param Tables *)
paramTables=Table[Panel[Panel[paramTable[dist[[i]]],channelNames[[i]],Background->channelColors[[i,2]]],Background->channelColors[[i,1]]],{i,1,3}];
valTables=Table[Panel[Panel[valTable[dist[[i]]["vars"],{{0,255},{0,255}}],channelNames[[i]],Background->channelColors[[i,2]]],Background->channelColors[[i,1]]],{i,1,3}];
(* Display Elements *)
numFrm=(NumberForm[#,4])&;
dispRules={"AxisColorStrips"->AxisColorStrips};
AppendTo[dispRules,"\[Delta]qS"->TraditionalForm[Row[{\[Delta]qS["\[Theta]'"]," = ","\[Delta]qS"/.distRules}]]];
AppendTo[dispRules,"L"->TraditionalForm[Row[{scale["LCaCb","nLCaCb"]["\[Theta]'"]," = ",MatrixForm@("L"/.distRules)}]]];
AppendTo[dispRules,"\[Delta]qEO"->TraditionalForm[Row[{\[Delta]qEO[MatrixForm@{0,a,b},"\[Theta]'"]," = ",MatrixForm@\[Delta]qEO[{0,a,b},"\[Theta]"/.distRules]}]]];
AppendTo[dispRules,"\[Kappa]"->Row[{\[Kappa]["\[Theta]'"]," = ",MatrixForm[("\[Kappa]"/.distRules)]}]];
AppendTo[dispRules,"tRange"->Row[{"tRange = ",MatrixForm[("tRange"/.distRules)]}]];
AppendTo[dispRules,"\[Lambda]RGB2"->TraditionalForm[Row[{\[Lambda]RGB2," = ",MatrixForm[(\[Lambda]RGB2["\[Theta]"/.distRules,"\[Lambda]"/.distRules])]}]]];
AppendTo[dispRules,"\[Alpha]\[Beta]"->TraditionalForm[Row[{MatrixForm[{0,\[Alpha],\[Beta]}]," = ",MatrixForm[{null,"\[Alpha]"/.distRules,"\[Beta]"/.distRules}]}]]];
AppendTo[dispRules,"\[Tau]"->TraditionalForm[Row[{\[Tau]," = ","Max[\[Alpha], \[Beta]]"^-1," \[TildeEqual] ","\[Tau]"/.distRules}]]];
(* Plot Elements *)
pbPlot=perturbationPlot[\[Theta]p,1,8,{"\[Alpha]"/.distRules,"\[Beta]"/.distRules},PlotRange->{Mod[\[Theta]p,Pi/6]-(Pi/84),Mod[\[Theta]p,Pi/6] + (Pi/84)}];
tol=Block[{accuracy},accuracy=0.01;Rationalize[accuracy Ceiling[1/(accuracy Max[{"\[Alpha]"/.distRules,"\[Beta]"/.distRules}])],accuracy]];
pb\[Tau]Plot=perturbationPlot[\[Theta]p,"\[Tau]"/.distRules,8,PlotRange->{Mod[\[Theta]p,Pi/6]-(Pi/84),Mod[\[Theta]p,Pi/6] + (Pi/84)}];

{valTables,paramTables,{(List@@pbPlot)[[1,1,1]],(List@@pbPlot)[[1,1,2,1]]},{(List@@pb\[Tau]Plot)[[1,1,1]],(List@@pb\[Tau]Plot)[[1,1,2,1]]},Grid[{{"AxisColorStrips",SpanFromLeft},{"L","\[Tau]"},{"\[Delta]qS","\[Delta]qEO"},{"\[Kappa]","tRange"},{"\[Lambda]RGB2","\[Alpha]\[Beta]"}},Frame->All]/.dispRules,
notes}
]


(* ::Section:: *)
(*The Points of Intersection.*)


(* ::Subsection::Closed:: *)
(*Init*)


CheckerBoardFromList[x_,y_,color_:Null,text_:Null,pos:{_,_}:{0,0},margin_:0.9]:=Module[{clr,txt,txtPos},
If[TrueQ[color==Null],clr=Table[ColorData[1][i j],{i,1,Length[x]-1,1},{j,1,Length[y]-1,1}],clr=color];
If[TrueQ[text==Null],
If[Length[y]>2&&Length[x]>2,
txt=Table[{i,j},{i,1,Length[x]-1,1},{j,1,Length[y]-1,1}],
txt=Table[i j,{i,1,Length[x]-1,1},{j,1,Length[y]-1,1}]],
txt=text];
Table[LabeldRectangle[{x[[i]],x[[i+1]]},{y[[j]],y[[j+1]]},txt[[i,j]],pos,margin,clr[[i,j]]],{i,1,Length[x]-1,1},{j,1,Length[y]-1,1}]
]


Clear[pntLabel];
pntLabel[{x_,y_},txt_,txtPos_,color_,bgColor_:RGBColor[1,1,1,0]]:={bgColor,Disk[{x,y},Scaled[{0.04, 0.04}]],Opacity[0.6,color],Disk[{x,y},Scaled[{0.005, 0.005}]],Opacity[1],Disk[{x,y},Scaled[{0.001, 0.001}]],Text[Style[TraditionalForm[txt],Medium,Bold,Darker[color,0.7]],{x,y},txtPos,{1,0},Background->None]}


(* ::Input:: *)
(*Graphics[CheckerBoardFromList[{0,1,2,3,4,5,6},{0,1,2}]]*)


approxSimplify=Function[{expr},Assuming[Element[m,Integers]&&m>0&&m<= n&&Element[n,Integers]&&n>3&&Element[\[Theta],Reals]&& \[Theta]>= 0 && \[Theta]< Pi&&Element[\[Delta]\[Theta],Reals]&& \[Delta]\[Theta]>= 0 && \[Delta]\[Theta]< Pi/6,FullSimplify[expr]]];


Format[maxA,TraditionalForm]="\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(\[Wedge]\)], \(a\)]\)";Format[minA,TraditionalForm]="\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(\[Vee]\)], \(a\)]\)";Format[maxB,TraditionalForm]="\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(\[Wedge]\)], \(b\)]\)";
Format[minB,TraditionalForm]="\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(\[Vee]\)], \(b\)]\)";Format[extremaA,TraditionalForm]="\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(o\)], \(a\)]\)";Format[extremaB,TraditionalForm]="\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(o\)], \(b\)]\)";
Format[interX,TraditionalForm]="\!\(\*OverscriptBox[\(\[Phi]\), \(x\)]\)";
Format[midM,TraditionalForm]="\!\(\*OverscriptBox[\(m\), \(_\)]\)";


ClearAll[extremaA,extremaB]
Format[extremaB[i__],TraditionalForm]:=Row[{"\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(o\)], \(b\)]\)",Style["("<>Riffle[Map[ToString[#,TraditionalForm]&,{i}],", "]<>")",Small]}];
Format[extremaA[i__],TraditionalForm]:=Row[{"\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(o\)], \(a\)]\)",Style["("<>Riffle[Map[ToString[#,TraditionalForm]&,{i}],", "]<>")",Small]}] ;
Row[{TraditionalForm[extremaA[5]],"    ",TraditionalForm[extremaB[5]]}]


(* ::Subsection::Closed:: *)
(*Init*)


\[Delta]qReFun=Function[{\[Theta]6,n},- Round[2^(-3+n) Sqrt[3] Tan[\[Theta]6]]+2^(-3+n) Sqrt[3] Tan[\[Theta]6]];
ClearAll[\[Delta]qRe]
\[Delta]qRe[\[Theta]:Except[_String],n_]:=\[Delta]qReFun[Mod[\[Theta],\[Pi]/6],n];
Format[\[Delta]qRe, TraditionalForm]=Style["\[Delta]qRe",Bold];



(* ::Input:: *)
(*ShowFun[\[Delta]qRe[\[Theta],n]]*)


Clear[perterbation,\[Theta]]
perterbation[\[Theta]:Except[_String],n_]:=Module[{},{{2 \[Delta]qRe[\[Theta],n],-2 \[Delta]qRe[\[Theta],n]},{2 \[Delta]qReFun[Pi/6 -Mod[\[Theta],\[Pi]/6],n],-2 \[Delta]qReFun[Pi/6 -Mod[\[Theta],\[Pi]/6],n]} }];
perterbation[\[Theta]_String,n_]:=Module[{},{{2 \[Delta]qRe[\[Theta],n],-2 \[Delta]qRe[\[Theta],n]},{2 \[Delta]qRe["Pi/6 -"<>\[Theta],n],-2 \[Delta]qRe["Pi/6 -"<>\[Theta],n]} }];


(* ::Input:: *)
(*TraditionalForm[Row[{perterbation["\[Theta]"]," = ",perterbation["\[Theta]",n]," = ",perterbation[\[Theta],n]}]]*)


Block[{i,n,m,\[Theta],y},
thetaIntersectionFun=Function[{m,n},Evaluate[FullSimplify[{\[Theta],Abs[perterbation[\[Theta],n][[1,1]]]}/.\[Theta]-> (ArcTan[(-7+2 y+Sqrt[49-4 y+4 y^2])/(2 Sqrt[3])]/.{y-> m 2^(2-n)})]]];
ClearAll[thetaIntersection];
thetaIntersection[m:Except[_String],n_]:=thetaIntersectionFun[m,n];
Format[thetaIntersection, TraditionalForm]=Style["\!\(\*OverscriptBox[\(\[Phi]\), \(x\)]\)",Bold];
]


(* ::Input:: *)
(*MatrixForm[ShowFun[thetaIntersection[m,n]]]*)


thetaIntersections=Function[{n}, Table[thetaIntersection[i,n],{i,0,2^(n-2)}]];


Block[{i,n,m,\[Theta],y},
\[Theta]ToIndxFun=Function[{\[Theta],n},Evaluate[FullSimplify[i/.Flatten[Solve[\[Theta]==thetaIntersection[i,n][[1]],i]]]]];
Clear[\[Theta]ToIndx];
\[Theta]ToIndx[\[Theta]:Except[_String],n_]:=\[Theta]ToIndxFun[\[Theta],n];
Format[\[Theta]ToIndx, TraditionalForm]=Style["i",Bold];
];


(* ::Input:: *)
(*ShowFun[\[Theta]ToIndx[\[Theta],n]]*)


thetaFun=Function[{y},{ArcTan[(Sqrt[3] y)/(4-y)],ArcTan[y/Sqrt[3]]},Listable];


(* ::Subsubsection::Closed:: *)
(*Minima *)
(*\!\(\*OverscriptBox[\(\[Phi]\), \(\[Vee]\)]\)*)


thetaMinFun=Function[{m,n},Evaluate[Simplify[thetaFun[m  2^(3-n)]]]];
Clear[thetaMin]
thetaMin[m:Except[_String],n:Except[_String]]:=thetaMinFun[m,n];
Format[thetaMin, TraditionalForm]=Style["\!\(\*OverscriptBox[\(\[Phi]\), \(\[Vee]\)]\)",Bold];


(* ::Input:: *)
(*ShowFun[thetaMin[m,n]]*)


thetaMinAFun=Function[{m,n},ArcTan[(2 Sqrt[3] m)/(2^n-2 m)]];
Clear[thetaMinA]
thetaMinA[m:Except[_String],n:Except[_String]]:=thetaMinAFun[m,n];
Format[thetaMinA, TraditionalForm]=Style["\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(\[Vee]\)], \(a\)]\)",Bold];


(* ::Input:: *)
(*ShowFun[thetaMinA[m,n]]*)


thetaMinBFun=Function[{m,n},ArcTan[(2^(3-n) m)/Sqrt[3]]];
Clear[thetaMinB]
thetaMinB[m:Except[_String],n:Except[_String]]:=thetaMinBFun[m,n];
Format[thetaMinB, TraditionalForm]=Style["\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(\[Vee]\)], \(b\)]\)",Bold];


(* ::Input:: *)
(*ShowFun[thetaMinB[m,n]]*)


(* ::Subsubsection::Closed:: *)
(*Maxima *)
(*\!\(\*OverscriptBox[\(\[Phi]\), \(\[Wedge]\)]\)*)


thetaMaxFun=Function[{m,n},Evaluate[Simplify[thetaFun[(m +1/2) 2^(3-n)]]]];
Clear[thetaMax]
thetaMax[m:Except[_String],n:Except[_String]]:=thetaMaxFun[m,n];
Format[thetaMax, TraditionalForm]=Style["\!\(\*OverscriptBox[\(\[Phi]\), \(\[Wedge]\)]\)",Bold];


(* ::Input:: *)
(*ShowFun[thetaMax[m,n]]*)


thetaMaxAFun=Function[{m,n},ArcTan[(Sqrt[3] (1+2 m))/(-1+2^n-2 m)]];
Clear[thetaMaxA]
thetaMaxA[m:Except[_String],n:Except[_String]]:=thetaMaxAFun[m,n];
Format[thetaMaxA, TraditionalForm]=Style["\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(\[Wedge]\)], \(a\)]\)",Bold];


(* ::Input:: *)
(*ShowFun[thetaMaxA[m,n]]*)


thetaMaxBFun=Function[{m,n},ArcTan[(2^(2-n) (1+2 m))/Sqrt[3]]];
Clear[thetaMaxB]
thetaMaxB[m:Except[_String],n:Except[_String]]:=thetaMaxBFun[m,n];
Format[thetaMaxB, TraditionalForm]=Style["\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(\[Wedge]\)], \(b\)]\)",Bold];


(* ::Input:: *)
(*ShowFun[thetaMaxB[m,n]]*)


(* ::Subsubsection::Closed:: *)
(*Extrema *)
(*\!\(\*OverscriptBox[\(\[Phi]\), \(o\)]\)*)


thetaExtremaFun=Function[{i,n},Evaluate[Simplify[thetaFun[(i/2) 2^(3-n)]]]];
Clear[thetaExtrema]
thetaExtrema[i:Except[_String],n:Except[_String]]:=thetaExtremaFun[i,n];
Format[thetaExtrema, TraditionalForm]=Style["\!\(\*OverscriptBox[\(\[Phi]\), \(o\)]\)",Bold];


(* ::Input:: *)
(*ShowFun[thetaExtrema[m,n]]*)


thetaExtremaAFun=Function[{i,n},ArcTan[(Sqrt[3] i)/(2^n-i)]];
Clear[thetaExtremaA];
Format[thetaExtremaA[i__],TraditionalForm]:=Row[{"\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(o\)], \(a\)]\)",Style["("<>Riffle[Map[ToString[#,TraditionalForm]&,{i}],", "]<>")",Small]}] ;
thetaExtremaA[i:Except[_String],n:Except[_String]]:=thetaExtremaAFun[i,n];


(* ::Input:: *)
(*ShowFun[thetaExtremaA[i,n]]*)


thetaExtremaBFun=Function[{i,n},ArcTan[(2^(2-n) i)/Sqrt[3]]];
Clear[thetaExtremaB];
Format[thetaExtremaB[i__],TraditionalForm]:=Row[{"\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(o\)], \(b\)]\)",Style["("<>Riffle[Map[ToString[#,TraditionalForm]&,{i}],", "]<>")",Small]}] ;
thetaExtremaB[i:Except[_String],n:Except[_String]]:=thetaExtremaBFun[i,n];


(* ::Input:: *)
(*ShowFun[thetaExtremaB[i,n]]*)


(* ::Subsubsection::Closed:: *)
(*Misc*)


midIFun=Function[{n},2^(n-3)];
Clear[midI]
midI[n:Except[_String]]:=midIFun[n];
Format[midI, TraditionalForm]=Style["\!\(\*OverscriptBox[\(i\), \(_\)]\)",Bold];


(* ::Input:: *)
(*ShowFun[midI[n]]*)


thetaFlipEFun=Function[{\[Iota],n},Sqrt[2^(2 (n-3))-14 2^(n-3) \[Iota]+ \[Iota]^2]];
Clear[thetaFlipE]
thetaFlipE[\[Iota]:Except[_String],n:Except[_String]]:=thetaFlipEFun[\[Iota],n];
Format[thetaFlipE, TraditionalForm]=Style["\[CapitalGamma]",Bold];


(* ::Input:: *)
(*ShowFun[thetaFlipE[\[Iota],n]]*)


MaxFlips=Function[{n},Floor[N[2^(-3+n) (7-4 Sqrt[3])]]];


indxTo\[Theta]=Function[{i,n},i 2^(2-n) Pi/6,Listable];
indxFlips=Function[{n},Evaluate[Table[{midI[n]-thetaFlipEFun[\[Iota],n],midI[n]+thetaFlipEFun[\[Iota],n]},{\[Iota],0,MaxFlips[n]}]]];


FlipRegionFun=Function[{i,n},Floor[7 2^(-3+n) -Sqrt[49 4^(-3+n)-2^(-2+n) i+i^2]]];
ClearAll[FlipRegion]
Format[FlipRegion[i_,n_], TraditionalForm]:=Style[Subsuperscript["\[Iota]",i,n],Bold];
FlipRegion[i:Except[_String],n_]:=FlipRegionFun[i,n];


(* ::Input:: *)
(*ShowFun[FlipRegion[i,n]]*)


ClearAll[genInterX,genInterXFun]
genInterXFun=Function[{\[Alpha],\[Beta],i,\[Iota],n,oddQI,oddQIota},
If[Xnor[oddQI,oddQIota],
{(\[Alpha] thetaExtremaA[i+\[Iota],n] (thetaExtremaB[-1+i-\[Iota],n]-thetaExtremaB[i-\[Iota],n])+\[Beta] (thetaExtremaA[i+\[Iota],n]-thetaExtremaA[1+i+\[Iota],n]) thetaExtremaB[i-\[Iota],n])/(\[Beta] (thetaExtremaA[i+\[Iota],n]-thetaExtremaA[1+i+\[Iota],n])+\[Alpha] (thetaExtremaB[-1+i-\[Iota],n]-thetaExtremaB[i-\[Iota],n])),(\[Alpha] \[Beta] (thetaExtremaA[i+\[Iota],n]-thetaExtremaB[i-\[Iota],n]))/(\[Beta] (thetaExtremaA[i+\[Iota],n]-thetaExtremaA[1+i+\[Iota],n])+\[Alpha] (thetaExtremaB[-1+i-\[Iota],n]-thetaExtremaB[i-\[Iota],n]))},
{(\[Beta] (thetaExtremaA[i+\[Iota],n]-thetaExtremaA[1+i+\[Iota],n]) thetaExtremaB[-1+i-\[Iota],n]+\[Alpha] thetaExtremaA[1+i+\[Iota],n] (thetaExtremaB[-1+i-\[Iota],n]-thetaExtremaB[i-\[Iota],n]))/(\[Beta] (thetaExtremaA[i+\[Iota],n]-thetaExtremaA[1+i+\[Iota],n])+\[Alpha] (thetaExtremaB[-1+i-\[Iota],n]-thetaExtremaB[i-\[Iota],n])),(\[Alpha] \[Beta] (-thetaExtremaA[1+i+\[Iota],n]+thetaExtremaB[-1+i-\[Iota],n]))/(\[Beta] (thetaExtremaA[i+\[Iota],n]-thetaExtremaA[1+i+\[Iota],n])+\[Alpha] (thetaExtremaB[-1+i-\[Iota],n]-thetaExtremaB[i-\[Iota],n]))}
]
];
genInterX[\[Alpha]:Except[_String],\[Beta]_,i_,\[Iota]_,n_]:=Module[{},
genInterXFun[\[Alpha],\[Beta],i,\[Iota],n,OddQ[i],OddQ[\[Iota]]]
];
genInterX[\[Alpha]:Except[_String],\[Beta]_,i_Integer,n_Integer]:=Module[{\[Iota]},
\[Iota]=FlipRegion[i,n];
genInterXFun[\[Alpha],\[Beta],i,\[Iota],n,OddQ[i],OddQ[\[Iota]]]
];
genInterX[\[Alpha]:Except[_String],\[Beta]_,i:Except[_Integer],n_]:=Module[{\[Iota]},
\[Iota]=FlipRegion[i,n];
genInterXFun[\[Alpha],\[Beta],i,\[Iota],n,"oddQ"[i],"oddQ"[\[Iota]]]
];
Format[genInterX[\[Alpha]\[Beta]__,i_,n_],TraditionalForm]:=Row[{Subsuperscript["\!\(\*OverscriptBox[\(\[Phi]\), \(X\)]\)",i,n],Style["("<>Riffle[Map[ToString[#,TraditionalForm]&,{\[Alpha]\[Beta]}],", "]<>")",Small]}]
Format[genInterX[i_,n_],TraditionalForm]:=Row[{Subsuperscript["\!\(\*OverscriptBox[\(\[Phi]\), \(X\)]\)",i,n]}]


(* ::Input:: *)
(*ShowFun[genInterX[\[Alpha],\[Beta],"i","n"]]*)


ClearAll[extremaA,extremaB]
Format[extremaB[i_],TraditionalForm]:=Row[{"\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(o\)], \(b\)]\)",Style["("<>ToString[i,TraditionalForm]<>")",Small]}];
Format[extremaA[i_],TraditionalForm]:=Row[{"\!\(\*SubscriptBox[OverscriptBox[\(\[Phi]\), \(o\)], \(a\)]\)",Style["("<>ToString[i,TraditionalForm]<>")",Small]}] ;
Row[{TraditionalForm[extremaA[5]],"    ",TraditionalForm[extremaB[5]]}]


perterbationLegend[colors_]:=Module[{},
If[Length[colors]>2,
SwatchLegend[colors, Map[TraditionalForm,{"2 \[Delta]qRe"["\[Delta]\[Theta]"],"-2 \[Delta]qRe"["\[Delta]\[Theta]"],"2 \[Delta]qRe"[Pi/6 -"\[Delta]\[Theta]"],"-2 \[Delta]qRe"[Pi/6 -"\[Delta]\[Theta]"]}] ],
SwatchLegend[colors, Map[TraditionalForm,{"\[PlusMinus]2 \[Delta]qRe"["\[Delta]\[Theta]"],"\[PlusMinus]2 \[Delta]qRe"[Pi/6 -"\[Delta]\[Theta]"]}] ]
]]


Clear[perturbationPlot];
Options[perturbationPlot]={PlotRange-> {0,Pi/6}};
perturbationPlot[theta_,\[Tau]_:0.5,n_:8, \[Alpha]\[Beta]:{_, _}:{1,1},OptionsPattern[]]:=Module[{pltRange,indxRange,minAf,minBf,maxAf,maxBf,pts,bColor=Green,aColor=Red,\[Delta]\[Theta],\[CapitalTheta],
maxAs,minAs,maxBs,minBs,pntA,pntB,interXs,interXPts,boundarys,ThetaBoundarys,iota,iotaBg,\[Phi]Ticks,title,selectX,selectXindx,selectXindxPrint,selectXTable,plt,valTable},
\[Delta]\[Theta]=Mod[theta,Pi/6]; 
\[CapitalTheta]=Quotient[theta,Pi/6] Pi/6;
pltRange=OptionValue[PlotRange];
indxRange={Ceiling[N[\[Theta]ToIndx[pltRange[[1]],n]]],Floor[N[\[Theta]ToIndx[pltRange[[2]],n]]]};
maxAs=Table[{pntLabel[{thetaExtremaA[i,n],\[Alpha]\[Beta][[2]]},extremaA[i],{0,1}, aColor], pntLabel[{thetaExtremaA[i,n],-\[Alpha]\[Beta][[2]]},extremaA[i],{0,1}, aColor]}, {i,1,2^(n-2)-1,2}];
minAs=Table[ pntLabel[{thetaExtremaA[i,n],0},extremaA[i],{0,1}, aColor], {i,2,2^(n-2)-1,2}];
maxBs=Table[{pntLabel[{thetaExtremaB[i,n],\[Alpha]\[Beta][[1]]},extremaB[i],{0,-1}, bColor], pntLabel[{thetaExtremaB[i,n],-\[Alpha]\[Beta][[1]]},extremaB[i],{0,-1}, bColor]}, {i,1,2^(n-2)-1,2}];
minBs=Table[ pntLabel[{thetaExtremaB[i,n],0},extremaB[i],{0,-1}, bColor], {i,2,2^(n-2)-1,2}];
If[\[Alpha]\[Beta]=={1,1},
interXPts=Table[thetaIntersection[i,n],{i,indxRange[[1]],indxRange[[2]],1}];
interXs=Table[pntA=interXPts[[i]]; pntB={1,-1}interXPts[[i]]; ii=i+indxRange[[1]]-1;{
pntLabel[pntA,thetaIntersection[ii],If[pntA[[2]]< \[Tau],{0,-1},{0,1}],If[pntA[[2]]< \[Tau],RGBColor[1/3,1/3,1,1],Darker[Blue]],If[pntA[[2]]< \[Tau],RGBColor[1,1,1,0.6],RGBColor[2/3,2/3,1,0]]],
pntLabel[pntB,thetaIntersection[ii],If[pntB[[2]]<-\[Tau],{0,-1},{0,1}],If[pntB[[2]]>-\[Tau],RGBColor[1/3,1/3,1,1],Darker[Blue]],If[pntB[[2]]>-\[Tau],RGBColor[1,1,1,0.6],RGBColor[2/3,2/3,1,0]]]}
,{i,1,Length[interXPts],1}];
,
interXPts=Table[genInterX[\[Alpha]\[Beta][[1]],\[Alpha]\[Beta][[2]],i,n],{i,indxRange[[1]],indxRange[[2]],1}];
 interXs=Table[pntA=interXPts[[i]]; pntB={1,-1}interXPts[[i]]; ii=i+indxRange[[1]]-1;
 {pntLabel[pntA,genInterX[ii,n],If[pntA[[2]]< \[Tau],{0,-1},{0,1}],If[pntA[[2]]< \[Tau],RGBColor[1/3,1/3,1,1],Darker[Blue]],If[pntA[[2]]< \[Tau],RGBColor[1,1,1,0.6],RGBColor[2/3,2/3,1,0]]]
 ,pntLabel[pntB,genInterX[ii,n],If[pntB[[2]]<-\[Tau],{0,-1},{0,1}],If[pntB[[2]]>-\[Tau],RGBColor[1/3,1/3,1,1],Darker[Blue]],If[pntB[[2]]>-\[Tau],RGBColor[1,1,1,0.6],RGBColor[2/3,2/3,1,0]]]
},{i,1,Length[interXPts],1}];
];
boundarys=Sort[Flatten[N[indxFlips[n]]]];
ThetaBoundarys=Evaluate[indxTo\[Theta][boundarys,n]];
iota=Flatten[{Table[\[Iota],{\[Iota],0,MaxFlips[n]}],Table[\[Iota],{\[Iota],MaxFlips[n]-1,0,-1}]}];
iotaBg=CheckerBoardFromList[ThetaBoundarys,{-Max[\[Alpha]\[Beta]],Max[\[Alpha]\[Beta]]}, 
         Table[ColorData[1][iota[[i]]],{i,1,Length[ThetaBoundarys]-1,1},{j,1,1,1}],
         Table[Row[{"\[Iota] = ",iota[[i]]}],{i,1,Length[ThetaBoundarys]-1,1},{j,1,1,1}], {0,-1}, 0.9];
\[Phi]Ticks=ReleaseHold[Table[
If[thetaIntersection[i,n][[2]]<=1,{N[thetaIntersection[i,n][[1]]],TraditionalForm[thetaIntersection[i]]},Hold[Sequence[]]]
,{i,0,2^(n-2),1}]];
title=Column[{Row[{"Perturbation to channels a and b against angle \[Delta]\[Theta]"}], Row[{"For n =",n,"  with \[Iota] regions shaded and extrema labeled"}]}];
selectX=Select[interXPts,(#[[2]]<\[Tau])&];
selectXindx=Map[(Round[N[\[Theta]ToIndx[#[[1]],n]]])&,selectX];
selectXindxPrint = Map[TraditionalForm[thetaIntersection[#]]&,selectXindx];
selectXTable=Panel[TableForm[Transpose[{
  Map[NumberForm[N[(#+\[CapitalTheta])],{4,4}] &,selectX[[All,1]]],
  Map[("\[PlusMinus]"<>ToString[NumberForm[#,{4,4}]])&,N[selectX[[All,2]]]],
  Map[ToString[NumberForm[N[(#-Mod[theta,Pi/6]) 180/Pi],{4,4},NumberSigns->{"-","+"}]]<>"\[Degree]"&,selectX[[All,1]]]}],
  TableHeadings->{selectXindxPrint,{"\[Theta]'","Perturbation","Change in \[Theta]"}},TableAlignments->Center],"Values of \[Theta] which produce a perturbation less than \[Tau]"];
valTable=Column[{
Panel[Row[{Grid[{{"\[Theta]","\[CapitalTheta]","\[Delta]\[Theta]","\[Tau]"},{NumberForm[theta,{4,4}],\[CapitalTheta],NumberForm[\[Delta]\[Theta],{4,4}],\[Tau]}},Frame->All]}],"\[Theta] = \[CapitalTheta] + \[Delta]\[Theta]"],
Panel[Row[{ToString[NumberForm[N[(pltRange[[1]]) 180/Pi],{2,2},NumberSigns->{"-","+"}]]<>"\[Degree]"," < ","\[Theta]'"," < ",ToString[NumberForm[N[(pltRange[[2]]) 180/Pi],{2,2},NumberSigns->{"-","+"}]]<>"\[Degree]"}],"Acceptable Values for \[Theta]'"],
selectXTable}];
plt=Plot[Evaluate[Flatten[\[Alpha]\[Beta] perterbation[\[Theta],n]]],{\[Theta],pltRange[[1]],pltRange[[2]]},
  PlotStyle->{ bColor,Darker[ bColor], aColor,Darker[ aColor]}, 
  PlotLabel-> title,Frame->True,FrameLabel->{{"Perturbation",None},{"\[Delta]\[Theta]",None}},
  FrameTicks->{{FracTicks[-2,2,2],{{\[Tau],"\[Tau]"},{-\[Tau],"-\[Tau]"}}},{Append[PiTicks[pltRange[[1]],pltRange[[2]],8],{\[Delta]\[Theta],"\[Delta]\[Theta]",{0.01`,0},GrayLevel[0]}],ReleaseHold[Table[Hold[Sequence][{(ThetaBoundarys[[i]]+ThetaBoundarys[[i-1]])/2,Row[{"\[Iota] = ",i-2}] },ThetaBoundarys[[i]] ],{i,2,Length[ThetaBoundarys]}]]}},
  Epilog->Flatten[{maxBs,minBs,maxAs,minAs,interXs,Black,Inset[Panel[perterbationLegend[{bColor, aColor}],Background->Opacity[0.7,White]],Scaled[{.95,.1}],{Right,Bottom}]}]];
Grid[{{Show[{plt,Graphics[maxBs],Graphics[{Opacity[0.5],iotaBg}],plt,Graphics[{Opacity[1],Black,Line[{{\[Delta]\[Theta],-Max[\[Alpha]\[Beta]]-0.3},{\[Delta]\[Theta],Max[\[Alpha]\[Beta]]+0.3}}],Line[{{pltRange[[1]],-\[Tau]},{pltRange[[2]],-\[Tau]}}],Line[{{pltRange[[1]],\[Tau]},{pltRange[[2]],\[Tau]}}]}]}],valTable}},Alignment->{Left,Top}]
]


(* ::Input:: *)
(*indxRange*)


(* ::Input:: *)
(*interXPts*)


(* ::Input:: *)
(*perturbationPlot[\[Theta]p,1,8,{1.2,0.8},PlotRange->{Mod[\[Theta]p,Pi/6]-(Pi/84),Mod[\[Theta]p,Pi/6] + (Pi/84)}]*)


(* ::Input:: *)
(*perturbationPlot[N[Pi/6+Pi/24],1/2,8,{2.5,2},PlotRange->{0,Pi/12}]*)


(* ::Section:: *)
(*Bin Visualisations.*)


(* ::Subsubsection::Closed:: *)
(*The Cube objects method for 3D bin plots.*)


(* ::Text:: *)
(*Test Color setup; the two images should look the same.*)


BinPlot3D[bin_,"RGB",tolZero:_:N[1/256],step_:1]:=Module[{r,g,b,rMax,gMax,bMax,minL,maxL,minO,val,vals,LCaCb,LCaCbA,rgb,fBin},
minL=0.2;(*Black is ok but hard to print*)
maxL=0.8;(* we cant see white on white *)
minO=0.03;(* Opacity min*)
{rMax,gMax,bMax}=Dimensions[bin["fBin"]];
Flatten[{EdgeForm[],Table[
vals= Flatten[(bin["fBin"])[[r;;r+step-1,g;;g+step-1,b;;b+step-1]]];
val=Total[vals]/Length[vals];
If[val>tolZero,
{RGBColor[{r/rMax,g/gMax,b/bMax,(1.-minO)  val+minO}],
Cuboid[{r-1,g-1,b-1},{r+step-1,g+step-1,b+step-1}]
}]
,{r,1,rMax,step},{g,1,gMax,step},{b,1,bMax,step}]}]/.Null-> Sequence[]
]
BinPlot3D[bin_,"LCaCb",tolZero:_:N[1/256],step_:1,\[Theta]_:0]:=Module[{l,Ca,Cb,lMax,CaMax,CbMax,minL,maxL,minO,val,vals,LCaCb,LCaCbA,rgb,fBin},
SetUpLCaCbColor["LCaCbColor",\[Theta]];
minL=0.2;(*Black is ok but hard to print*)
maxL=0.8;(* we cant see white on white *)
minO=0.03;(* Opacity min*)
{lMax,CaMax,CbMax}=Dimensions[bin["fBin"]];
Flatten[{EdgeForm[],Table[
vals= Flatten[(bin["fBin"])[[l;;l+step-1,Ca;;Ca+step-1,Cb;;Cb+step-1]]];
val=Total[vals]/Length[vals];
If[val>tolZero,
{LCaCbColor[{l/(lMax) (maxL-minL)+minL,Ca/CaMax,Cb/CbMax,(1.-minO)  val+minO}],
Cuboid[{l-1,Ca-1,Cb-1},{l+step-1,Ca+step-1,Cb+step-1}]
}]
,{l,1,lMax,step},{Ca,1,CaMax,step},{Cb,1,CbMax,step}]}]/.Null-> Sequence[]
]


Clear[HistoPlot3D]
Options[HistoPlot3D]={ColorFunction->Function[{Ca,Cb,val},Evaluate[LCaCbColor[0.7,Ca,Cb,val]]],\[Theta]->0};
HistoPlot3D[bin_,"LCaCb",tolZero:_:N[1/256],drIn_:{},OptionsPattern[] ]:=Module[{l,Ca,Cb,lMax,CaMax,CbMax,minL,maxL,minO,val,vals,LCaCb,LCaCbA,rgb,dr,clrFun},
SetUpLCaCbColor["LCaCbColor",OptionValue[\[Theta]] ];
minL=0.2;(*Black is ok but hard to print*)
maxL=0.8;(* we cant see white on white *)
minO=0.3;(* Opacity min*)
{CaMax,CbMax}=Dimensions[bin["fBin"]];
If[Length[drIn]==0,dr={{1,CaMax},{1,CbMax}},dr=drIn];
clrFun=OptionValue[ColorFunction];
Flatten[{EdgeForm[],
Table[val=bin["fBin"][[Ca,Cb]];
If[val>0.001,{EdgeForm[],clrFun[Ca/CaMax,Cb/CbMax,(1.-minO)  val+minO],Cuboid[{Ca-0.5,Cb-0.5,0},{Ca+0.5,Cb+0.5, bin["fBin"][[Ca,Cb]]}]}],{Cb,dr[[2,1]],dr[[2,2]]},{Ca,dr[[1,1]],dr[[1,2]]}]/.{Null->Sequence[],Indeterminate->0}
}]
]


Clear[BinPlot2D]
BinPlot2D[bin_,"LCaCb",tolZero:_:N[1/256],step_:1,\[Theta]_:0]:=Module[{l,Ca,Cb,CaMax,CbMax,minL,maxL,minO,val,vals,LCaCb,LCaCbA,rgb,fBin},
SetUpLCaCbColor["LCaCbColor",\[Theta]];
minL=0.2;(*Black is ok but hard to print*)
maxL=0.8;(* we cant see white on white *)
minO=0.03;(* Opacity min*)
{CaMax,CbMax}=Dimensions[bin["fBin"]];
l=0.5;
Flatten[{EdgeForm[],Table[
vals= Flatten[(bin["fBin"])[[Ca;;Ca+step-1,Cb;;Cb+step-1]]];
val=Total[vals]/Length[vals];
If[val>tolZero,
{LCaCbColor[{l,Ca/CaMax,Cb/CbMax,(1.-minO)  val+minO}],
Rectangle[{Ca-1,Cb-1},{Ca+step-1,Cb+step-1}]
}]
,{Ca,1,CaMax,step},{Cb,1,CbMax,step}]}]/.{Null-> Sequence[],Indeterminate->0}
]


Clear[genAnimation]
genAnimation[bin_,{\[Theta]s_,\[Theta]e_},{\[Phi]s_,\[Phi]e_},frames_]:=Module[{i,\[Theta],\[Phi]=Pi/3,step\[Theta],step\[Phi]},
step\[Theta]=(\[Theta]e-\[Theta]s)/frames;
step\[Phi]=(\[Phi]e-\[Phi]s)/frames;
Table[
\[Theta]=\[Theta]s+i step\[Theta];
\[Phi]=\[Phi]s+i step\[Phi];
Rasterize[Graphics3D[bin["PlotData"],
Method->{"CuboidPoints"->4},AlignmentPoint->{0,0},Boxed->True,ViewCenter->Center,ViewAngle->Pi/7,ViewPoint-> {4 Sin[\[Theta]],4 Cos[\[Theta]] Sin[\[Phi]],4 Cos[\[Phi]]},Axes->True,AxesEdge->{{-1,-1},{-1,-1},{-1,-1}},AxesLabel->bin["axisNames"],ImagePadding->{{2,2},{2,2}},ImageSize->400,ImageMargins->2,PlotRange-> bin["PlotRange"],ViewVertical->{1,0, 0},PlotLabel-> bin["PlotLabel"]]],{i,0,frames,1}]
];


boundBox[bin_]:={EdgeForm[{Black,Thick}],FaceForm[],Cuboid[{(bin["aMin"]),(bin["aMax"])}]};
skinnedBox[bin_,skinDepth_]:={EdgeForm[{Black,Thick}],FaceForm[],Cuboid[{(bin["aMin"])+skinDepth, (bin["aMax"])-skinDepth}]};


topAndTailBox[bin_,depth_]:={EdgeForm[{Black,Thick}],FaceForm[{White,Opacity[0.4]}],Cuboid[{(bin["aMin"]),{(bin["aMin"])[[1]]+depth,(bin["aMax"])[[2]],(bin["aMax"])[[3]]}}],Cuboid[{{(bin["aMax"])[[1]]-depth,(bin["aMin"])[[2]],(bin["aMin"])[[3]]},(bin["aMax"])}]};


projectedView[bin_,extra_:{},n_,opts:OptionsPattern[Graphics3D]]:=Module[{viewPoint,axesLabel,axesEdge},
axesEdge={{-1,-1},{-1,-1},{-1,-1}}; axesEdge[[n]]=None;
axesLabel=bin["axisNames"]; axesLabel[[n]]="";
viewPoint={0,0,0}; If[n>0,viewPoint[[n]]=Infinity,viewPoint[[Abs[n]]]=-Infinity];
Rasterize[Graphics3D[{bin["PlotData"],extra},Method->{"CuboidPoints"->4},Axes->True,AxesEdge->axesEdge,AxesLabel->axesLabel,ViewPoint->viewPoint,Lighting->"Neutral",opts]]]


Clear[GaussianFitFun];
GaussianFitFun[x_,y_,\[Mu]_,\[Sigma]_,\[Theta]_]:=Module[{xrot,yrot,\[Mu]rot,\[Phi]},
(* \[Phi]=Pi-\[Theta]; *)
\[Phi]=Pi-\[Theta];
xrot=x Cos[\[Phi]]-y Sin[\[Phi]];
yrot=x Sin[\[Phi]]+y Cos[\[Phi]];
\[Mu]rot={\[Mu][[1]]*Cos[\[Phi]]-\[Mu][[2]] Sin[\[Phi]],\[Mu][[1]] Sin[\[Phi]]+\[Mu][[2]]*Cos[\[Phi]]};
Exp[-((xrot-\[Mu]rot[[1]])^2/(2*\[Sigma][[1]]^2)+(yrot-\[Mu]rot[[2]])^2/(2*\[Sigma][[2]]^2))]
]



Clear[\[Mu]\[Sigma]\[Theta]FromBin];
\[Mu]\[Sigma]\[Theta]FromBin[bin_,order_:{1,2}]:=Block[{\[Mu],\[Sigma],\[Theta]},
\[Mu]={bin["gMean"  ][[order[[1]]]],bin["gMean"   ][[order[[2]]]]};
\[Sigma]={bin["gSigma"][[order[[1]]]],bin["gSigma"][[order[[2]]]]};
If[order=={1,2},\[Theta]=bin["gTheta"],\[Theta]=Pi-bin["gTheta"]];
{\[Mu],\[Sigma],\[Theta]}
]


Clear[swapMinorMajorAxis];
swapMinorMajorAxis[bin_]:=Block[{\[Mu],\[Sigma],\[Theta]},
\[Sigma]={bin["gSigma"][[2]],bin["gSigma"][[1]]};
\[Theta]=Mod[bin["gTheta"]+N[Pi/2],2 Pi];
bin["gSigma"]=\[Sigma];
bin["gTheta"]=\[Theta];
]


Clear[GaussianFit]
GaussianFit[bin_,order_:{1,2}]:=Module[{xx,yy,\[Mu],\[Sigma],\[Theta]},
{\[Mu],\[Sigma],\[Theta]} = \[Mu]\[Sigma]\[Theta]FromBin[bin,order];
Function[{xx,yy},Evaluate[GaussianFitFun[xx,yy,\[Mu],\[Sigma],\[Theta]]]]
];


Clear[MajorMinorAxesPoints];
MajorMinorAxesPoints[\[Mu]_,\[Sigma]_,\[Theta]_,sig_]:={
{{\[Mu][[1]]-sig \[Sigma][[1]] Cos[\[Theta]],\[Mu][[2]] -sig \[Sigma][[1]]Sin[\[Theta]] },{\[Mu][[1]]+sig \[Sigma][[1]]Cos[\[Theta]] ,\[Mu][[2]] +sig \[Sigma][[1]] Sin[\[Theta]] }},
{{\[Mu][[1]]-sig \[Sigma][[2]] Cos[\[Theta]-Pi/2],\[Mu][[2]] -sig \[Sigma][[2]]Sin[\[Theta]-Pi/2] },{\[Mu][[1]]+sig \[Sigma][[2]]Cos[\[Theta]-Pi/2] ,\[Mu][[2]] +sig \[Sigma][[2]] Sin[\[Theta]-Pi/2] }}};


Clear[dataRange]
If[$VersionNumber>9,
dataRange[bin_,"All",order_:{1,2}]:=Module[{axisTotalA,axisTotalB},
axisTotalA=Total[bin["fBin"],{1}];
axisTotalB=Total[bin["fBin"],{2}];
If[order=={1,2},fun=Sequence,fun=Reverse];
fun[{Flatten[{FirstPosition[axisTotalB,n_ /; n>0],
Length[axisTotalB]-FirstPosition[Reverse[axisTotalB],n_ /; n>0]}],Flatten[{FirstPosition[axisTotalA,n_ /; n>0],
Length[axisTotalA]-FirstPosition[Reverse[axisTotalA],n_ /; n>0]}]}]
],
dataRange[bin_,"All",order_:{1,2}]:=Module[{axisTotalA,axisTotalB},
axisTotalA=Total[bin["fBin"],{1}];
axisTotalB=Total[bin["fBin"],{2}];
If[order=={1,2},fun=Sequence,fun=Reverse];
fun[{Flatten[{First[Position[axisTotalB,n_ /; n>0]],
Length[axisTotalB]-First[Position[Reverse[axisTotalB],n_ /; n>0]]}],Flatten[{First[Position[axisTotalA,n_ /; n>0]],
Length[axisTotalA]-First[Position[Reverse[axisTotalA],n_ /; n>0]]}]}]
]
]
dataRange[bin_,sig_Integer,order_:{1,2}]:=Module[{\[Mu],\[Sigma],\[Theta],mmAxes},
{\[Mu],\[Sigma],\[Theta]} = \[Mu]\[Sigma]\[Theta]FromBin[bin,order];
mmAxes=MajorMinorAxesPoints[\[Mu],\[Sigma],\[Theta],sig];
{{Min[Flatten[mmAxes[[All,All,1]]]],
Max[Flatten[mmAxes[[All,All,1]]]]},{
Min[Flatten[mmAxes[[All,All,2]]]],
Max[Flatten[mmAxes[[All,All,2]]]]}}
]


Clear[ellipsePlot];
EllipseColor::usage="Option for ellipsePlot. the color of the ellipse";
Options[ellipsePlot]={EllipseColor-> Black};
ellipsePlot[bin_,sig:_Integer:5,order_:{1,2},opts:OptionsPattern[]]:=ellipsePlot[bin,{1,sig},order,opts]
ellipsePlot[bin_,sig:_List:{1,5},order_:{1,2},OptionsPattern[]]:=Module[{\[Mu],\[Sigma],\[Theta],mmAxes},
{\[Mu],\[Sigma],\[Theta]} = \[Mu]\[Sigma]\[Theta]FromBin[bin,order];
{EdgeForm[{OptionValue[EllipseColor]}],FaceForm[],Table[Rotate[Ellipsoid[\[Mu],i \[Sigma]],\[Theta]],{i,sig[[1]],sig[[2]]}]}
]


Clear[fitXPlt];
fitXPlt[bin_,sig_:5,order_:{1,2}]:=Module[{\[Mu],\[Sigma],\[Theta],x1,x2,f1,f2,pltRng},
{\[Mu],\[Sigma],\[Theta]} = \[Mu]\[Sigma]\[Theta]FromBin[bin,order];
pltRng = {Min[-(sig+0.2 )\[Sigma][[1]],-(sig+0.2 ) \[Sigma][[2]]],
               Max[   (sig+0.2 ) \[Sigma][[1]],   (sig+0.2 ) \[Sigma][[2]]]}+\[Mu][[1]];
Show[Table[
x1=\[Mu][[1]]-i \[Sigma][[1]];x2=\[Mu][[1]]+i \[Sigma][[1]];
f1=GaussianFitFun[x1,\[Mu][[2]],\[Mu],\[Sigma],0];
f2=GaussianFitFun[x2,\[Mu][[2]],\[Mu],\[Sigma],0];
{ListPlot[{{x1,f1},{x2,f2}},Frame->True,Axes->False,PlotStyle->Red],Graphics[{Text[i "\!\(\*SubscriptBox[\(\[Sigma]\), \(1\)]\)",{x1,f1},{1,-1}],Text[Style[ToString[i]<>"\!\(\*SubscriptBox[\(\[Sigma]\), \(1\)]\)",Small],{x2,f2},{-1,-1}]}]},{i,1,sig}],
Plot[GaussianFitFun[x,\[Mu][[2]],\[Mu],\[Sigma],0],{x,pltRng[[1]],pltRng[[2]]},AxesLabel->{"Ca'","Frequency"},PlotStyle->Red,PlotRange->{pltRng,{0,1}}],
PlotRange->{pltRng,{0,1}},FrameLabel->{{"Frequency",None},{"Ca'","The \!\(\*SubscriptBox[\(\[Sigma]\), \(1\)]\) Gaussian"}}]
];
Clear[fitYPlt];
fitYPlt[bin_,sig_:5,order_:{1,2}]:=Module[{\[Mu],\[Sigma],\[Theta],y1,y2,f1,f2,pltRng},
{\[Mu],\[Sigma],\[Theta]} = \[Mu]\[Sigma]\[Theta]FromBin[bin,order];
pltRng = {Min[-(sig+0.2 )\[Sigma][[1]],-(sig+0.2 ) \[Sigma][[2]]],
               Max[   (sig+0.2 ) \[Sigma][[1]],   (sig+0.2 ) \[Sigma][[2]]]}+\[Mu][[2]];
Show[
 Table[
y1=\[Mu][[2]]-i \[Sigma][[2]];y2=\[Mu][[2]]+i \[Sigma][[2]];
f1=GaussianFitFun[\[Mu][[1]],y1,\[Mu],\[Sigma],0];
f2=GaussianFitFun[\[Mu][[1]],y2,\[Mu],\[Sigma],0];
{ListPlot[{{y1,f1},{y2,f2}},Frame->True,Axes->False,PlotStyle->Green],Graphics[{Text[i "\!\(\*SubscriptBox[\(\[Sigma]\), \(2\)]\)",{y1,f1},{1,-1}],Text[Style[ToString[i]<>"\!\(\*SubscriptBox[\(\[Sigma]\), \(2\)]\)",Small],{y2,f2},{-1,-1}]}]},{i,1,sig}],
Plot[GaussianFitFun[\[Mu][[1]],y,\[Mu],\[Sigma],0],{y,pltRng[[1]],pltRng[[2]]},AxesLabel->{"Cb'","Frequency"},PlotStyle->Green,PlotRange->{pltRng,{0,1}}],
PlotRange->{pltRng,{0,1}},FrameLabel->{{"Frequency",None},{"Cb'","The \!\(\*SubscriptBox[\(\[Sigma]\), \(2\)]\) Gaussian"}}]
];



Clear[statTable]
Options[statTable]={Orientation-> "Horizontal"}
statTable[bin_,digits_:3,order_:{1,2},OptionsPattern[]]:=Block[{\[Mu],\[Sigma],\[Theta]},
{\[Mu],\[Sigma],\[Theta]} = \[Mu]\[Sigma]\[Theta]FromBin[bin,order];
If[OptionValue[Orientation]=="Horizontal",
Grid[{
{"",   Style["\[Theta]",Bold],Style["\[Mu]",Bold],Style["\[Sigma]",Bold]},
{"Ca'",NumberForm[\[Theta],digits] ,NumberForm[\[Mu][[1]],digits], NumberForm[\[Sigma][[1]], digits]},
{"Cb'",SpanFromAbove        ,NumberForm[\[Mu][[2]],digits], NumberForm[\[Sigma][[2]], digits]}
}, Frame->All,Alignment->{Center,Center},Background->RGBColor[1,1,1,0.6]],
Grid[{
{ Style["\[Theta]",Bold], NumberForm[\[Theta],digits],SpanFromLeft},
{Style["\[Mu]",Bold], "Ca", NumberForm[\[Mu][[1]],digits]},
{SpanFromAbove,   "Cb", NumberForm[\[Mu][[2]],digits]},
{Style["\[Sigma]",Bold], "Ca'", NumberForm[\[Sigma][[1]],digits]},
{SpanFromAbove,   "Cb'", NumberForm[\[Sigma][[2]],digits]}
}, Frame->All,Alignment->{Center,Center},Background->RGBColor[1,1,1,0.6] ]
]
]


Clear[fit2DLinesPlt]
Protect[AxisColor,MeanColor,TextColor];
Options[fit2DLinesPlt]={AxisColor-> {Red,Green},TextColor->Black, MeanColor->Blue,PointSize-> 0.25};
fit2DLinesPlt[bin_,sig_:5,order_:{1,2},OptionsPattern[]]:=Module[{sr,\[Mu]r=1, opcty=0.6},
sr= OptionValue[PointSize];
{\[Mu],\[Sigma],\[Theta]} = \[Mu]\[Sigma]\[Theta]FromBin[bin,order];
Do[mmAxes[i]=MajorMinorAxesPoints[\[Mu],\[Sigma],\[Theta],i],{i,1,sig}];
axesPltPnts={Opacity[opcty],OptionValue[MeanColor],Disk[\[Mu],sr],
OptionValue[AxisColor][[1]],Table[{Disk[mmAxes[i][[1,1]],sr],Disk[mmAxes[i][[1,2]],sr]},{i,1,sig}],
OptionValue[AxisColor][[2]], Table[{Disk[mmAxes[i][[2,1]],sr],Disk[mmAxes[i][[2,2]],sr]},{i,1,sig}]};
axesPltLines={Opacity[1],
OptionValue[AxisColor][[1]],Line[mmAxes[sig][[1]]],
OptionValue[AxisColor][[2]], Line[mmAxes[sig][[2]]]};
axesPltTxt={OptionValue[TextColor],
Table[{Text[Style[Subscript[i "\[Sigma]",Style["1",Small]],Bold,Medium],mmAxes[i][[1,1]],{1,1}],Text[Style[Subscript[i "\[Sigma]",Style["1",Small]],Bold,Medium],mmAxes[i][[1,2]],{-1,-1}]},{i,1,sig}],
Table[{Text[Style[Subscript[i "\[Sigma]",Style["2",Small]],Bold,Medium],mmAxes[i][[2,1]],{1,0}],Text[Style[Subscript[i "\[Sigma]",Style["2",Small]],Bold,Medium],mmAxes[i][[2,2]],{-1,0}]},{i,1,sig}],
Text[Style["\[Mu]",Bold],\[Mu]+{(-2sr /3) Cos[(Pi/2-\[Theta])],(-2sr /3)  Sin[(Pi/2-\[Theta])]}]};
{axesPltPnts,axesPltLines,axesPltTxt}
]



Clear[fit2DAnglePlt];
fit2DAnglePlt[bin_,order_:{1,2}]:=Module[{r=4, opcty=0.6,\[Theta]s,\[Theta]e,\[Phi]s,\[Phi]e},
{\[Mu],\[Sigma],\[Theta]} = \[Mu]\[Sigma]\[Theta]FromBin[bin,order];
\[Theta]s=0; \[Theta]e = \[Theta];
\[Phi]s=\[Theta]; \[Phi]e = Pi/2;
{Graphics[{Opacity[opcty],Green,
Disk[\[Mu],r,{\[Theta]s,\[Theta]e}],Opacity[1],Black,Text[Style["\[Theta]",Bold,Large],\[Mu]+{(2r /3) Cos[(\[Theta]e+\[Theta]s)/2],(2r /3)  Sin[(\[Theta]e+\[Theta]s)/2]}]}],
Graphics[{Opacity[opcty],Red,
Disk[\[Mu],r,{\[Phi]s,\[Phi]e}],Opacity[1],Black,Text[Style["\[Phi]",Bold,Large],\[Mu]+{(2r /3) Cos[(\[Phi]e+\[Phi]s)/2],(2r /3)  Sin[(\[Phi]e+\[Phi]s)/2]}]}]}
];


Clear[fitComparisonPlt]
Options[fitComparisonPlt]={ColorFunction->Function[{Ca,Cb,val},Evaluate[LCaCbColor[0.7,Ca,Cb,val]]],Margin-> 20};
fitComparisonPlt[bin_,order_:{1,2},OptionsPattern[]]:=Module[{CaMax,CbMax,dr,pltRng,boxRto,histoPlt,fun,fitPlt,combPlt3D},
{CaMax,CbMax}=Dimensions[bin["fBin"]];
clrFun=Function[{Ca,Cb,val},Evaluate[OptionValue[ColorFunction][Ca/CaMax,Cb/CbMax,val/1.1]]];
dr=Round[dataRange[bin,"All",order]];
pltRng = {dr[[1]]+{-OptionValue[Margin],OptionValue[Margin]},dr[[2]]+{-OptionValue[Margin],OptionValue[Margin]},{0,1}};
boxRto = Flatten[{N[(dr[[All,2]]-dr[[All,1]])/Max[dr[[All,2]]-dr[[All,1]]]],1}];
histoPlt=Graphics3D[HistoPlot3D[bin,"LCaCb",N[1/1024],dr,ColorFunction-> OptionValue[ColorFunction]],Lighting->"Neutral",Axes->True,AxesLabel->{"Ca","Cb","f"},BoxRatios->boxRto];
fun=GaussianFit[bin,order];
fitPlt=Plot3D[fun[x,y],{x,pltRng[[1,1]],pltRng[[1,2]]},{y,pltRng[[2,1]],pltRng[[2,2]]},PlotRange-> pltRng,PlotPoints->2 (dr[[1,2]]-dr[[1,1]]),ColorFunction->clrFun,ColorFunctionScaling->False,AxesLabel->{"Ca","Cb","f"},MeshFunctions->{#3&}];
combPlt3D=Show[{fitPlt,histoPlt},
PlotRange->pltRng,
BoxRatios->boxRto];
{{fitPlt,histoPlt}, {PlotRange->pltRng,
BoxRatios->boxRto}}
]


Clear[overlayElems]
Options[overlayElems]=Flatten[{AxisSigma->5,EllipsisSigma->{1,5},Options[fit2DLinesPlt],Options[ellipsePlot]}];
overlayElems[bin_,order_:{1,2},opts:OptionsPattern[]]:=Module[{axisPlt,elpsPlt,thetaPlt,phiPlt,aspctRatio,dr,combPltOpts},
axisPlt=Graphics[fit2DLinesPlt[bin,OptionValue[AxisSigma],order,FilterRules[{opts},Options[fit2DLinesPlt]]]];
elpsPlt=Graphics[ellipsePlot[bin,OptionValue[EllipsisSigma],order,FilterRules[{opts},Options[ellipsePlot]]]];
{thetaPlt,phiPlt}=fit2DAnglePlt[bin,order];

dr=dataRange[bin,Max[{OptionValue[EllipsisSigma][[2]],OptionValue[AxisSigma]}]];
aspctRatio=(dr[[2,2]]-dr[[2,1]])/(dr[[1,2]]-dr[[1,1]]);
combPltOpts={PlotRange->dr,AspectRatio->aspctRatio,Frame->True,FrameLabel->{"Ca","Cb"}};
{{axisPlt,elpsPlt,thetaPlt, phiPlt},combPltOpts}
];



Clear[gFitElems]
gFitElems[bin_,order_:{1,2}]:=Module[{redPlt,greenPlt,denPlt,denOpacityPlt,axesPlt,elpsPlt,thetaPlt,phiPlt,histoPlt,fitPlt,combPlt3D,combPlt3Dopts,combPlt,combPltOpts,overviewPlt,stat,fun,dr},
dr=dataRange[bin,5];
stat = statTable[bin,4,order];
redPlt    =fitXPlt[bin,5,order];
greenPlt=fitYPlt[bin,5,order];

denPlt=ListDensityPlot[bin["fBin"],AxesLabel->{"Cb","Ca"},InterpolationOrder->0];
denOpacityPlt=Graphics[bin["PlotData"],Frame->True,PlotRange-> bin["PlotRange"],FrameLabel->{{(bin["axisNames"])[[2]],""},{(bin["axisNames"])[[1]],"Overview"}}];

{{axesPlt,elpsPlt,thetaPlt, phiPlt},combPltOpts}=overlayElems[bin,order];
combPlt=Function[{incDen,incAxis,incElps,incTheta,incPhi,incStat},Show[{If[incDen,denOpacityPlt],If[incAxis,axesPlt],If[incElps,elpsPlt],If[incTheta,thetaPlt],If[incPhi,phiPlt]}/.Null->Sequence[],If[incStat,Append[combPltOpts,Epilog-> Inset[stat,Extract[OptionValue[Graphics,combPltOpts,PlotRange],{{1,1},{2,2}}],{Left,Top}]],combPltOpts]]];

{{fitPlt,histoPlt},combPlt3Dopts}=fitComparisonPlt[bin,{1,2},Margin-> 5 ];
combPlt3D=Function[{incFit,incHisto,incStat},Show[{If[incFit,fitPlt],If[incHisto,histoPlt]}/.Null->Sequence[],If[incStat,Append[combPlt3Dopts,Epilog-> Inset[stat,{Left,Top},{Left,Top}]],combPlt3Dopts]]];

overviewPlt=Show[{denOpacityPlt,
Graphics[{FaceForm[],EdgeForm[{Black,Opacity[1]}],Rectangle[{dr[[1,1]],dr[[2,1]]},{dr[[1,2]],dr[[2,2]]}]}]}];
{stat,redPlt,greenPlt,combPlt3D,combPlt,overviewPlt}
];



(* ::Subsubsection::Closed:: *)
(*Document Generation Routines*)


Clear[NotebookDefinitionWrite]
SetAttributes[NotebookDefinitionWrite,HoldAllComplete]
NotebookDefinitionWrite[nb_,var_]:=Module[{cell},
cell=Cell[BoxData[RowBox[{var,"=",ToBoxes[Symbol[var]],";"}]],"Input",InitializationCell->True];
NotebookWrite[nb,cell ]]


Clear[CellDefinitionWrite]
SetAttributes[CellDefinitionWrite,HoldAllComplete]
CellDefinitionWrite[var_]:=Module[{cell},
cell=Cell[BoxData[RowBox[{var,"=",ToBoxes[Symbol[var]],";"}]],"Input",InitializationCell->True];
CellPrint[cell ]]


exportPanelCell[outName_,fileName_]:=Module[{},
Cell[BoxData[RowBox[{"Panel","[",RowBox[{"Column","[",RowBox[{"{",RowBox[{
RowBox[{"Panel","[",RowBox[{outName,",",RowBox[{"Background","\[Rule]","White"}],",",RowBox[{"ImageSize","\[Rule]","1000"}]}],"]"}],",","\n",
RowBox[{"Button","[",RowBox[{"\"\<Export\>\"",",","\n",RowBox[{
RowBox[{"Export","[",RowBox[{RowBox[{"figPath","<>","\""<>fileName<>".jpg\""}],",",outName,",",RowBox[{"ImageResolution","\[Rule]","300"}]}],"]"}],";","\n",
RowBox[{"Export","[",RowBox[{RowBox[{"figPath","<>","\""<>fileName<>".eps\""}],",",outName}],"]"}],";","\n",
RowBox[{"Export","[",RowBox[{RowBox[{"figPath","<>","\""<>fileName<>".pdf\""}],",",outName}],"]"}]}]}],"]"}]}],"}"}],"]"}],"]"}]],"Code"]
]


BringToFront[list_,n_]:=Module[{tail,head},head=Take[list,n];tail=Drop[list,n];{Sequence@@head,Sequence@@tail}]


(* ::Section:: *)
(*Wavefunctions.*)


Options[chromaticPlane]={Frame->True,Title->True};
Clear[chromophoresLCaCb];
chromaticPlane[theta_,chromophoresRGB_:{{245,56,21},{251,51,8},{231,123,48},{239,119,31}},OptionsPattern[]]:=Module[
{minA,maxA,minB,maxB,chromoYAB,avgY,r,shift,align,nLCaCbChromophores,nLCaCbChromophoresPlane,title},
{{minA,maxA},{minB,maxB}}={{-0.5,0.5},{-0.5,0.5}};
chromoYAB=(Transpose[N[nLCaCb[theta].Transpose[chromophoresRGB/255]]]) ;
avgY= Plus@@chromoYAB[[All,1]]/4;
pts= 255 Map[(#+{0.5,0.5})&,chromoYAB[[All,2;;3]]];
r=255 0.02;
shift= {r+255 0.01,0};
align=Function[{a,b},If[Abs[a-b] < 2 r,If[a<b,{Left,Top},{Left,Bottom}],{Left,Center}]];
If[OptionValue[Title],title=Text[Style["Rotated ColorSpace with :\n\[Theta] = "<>ToString[theta]<>"\n L = "<>ToString[avgY],Medium],{minA+r,255 -r},{Left,Top}],title=Sequence[]];
If[OptionValue[Frame],
Graphics[{
Raster[Table[Table[inLCaCb[theta].{avgY,a,b},{a,minA,maxA,N[1/256]}],{b,minB,maxB,N[1/256]}],{{0,0},{255,255}}], title,
Circle[pts[[1]],r],Text[Style["Hb",  Medium],pts[[1]]+shift,align[pts[[1,2]],pts[[2,2]]] ],
Circle[pts[[2]],r],Text[Style["HbO2",Medium],pts[[2]]+shift,align[pts[[2,2]],pts[[1,2]]] ],
Circle[pts[[3]],r],Text[Style["Eumelanin",  Medium],pts[[3]]+shift,align[pts[[3,2]],pts[[4,2]]] ],
Circle[pts[[4]],r],Text[Style["Pheomelanin",Medium],pts[[4]]+shift,align[pts[[4,2]],pts[[3,2]]] ]},ImageSize->500,Frame->True, FrameTicks->{{BinaryTicks[0,256,3],BinaryTicks[0,256,3]},{BinaryTicks[0,256,3],BinaryTicks[0,256,3]}}]
,Graphics[{
Raster[Table[Table[inLCaCb[theta].{avgY,a,b},{a,minA,maxA,N[1/256]}],{b,minB,maxB,N[1/256]}],{{0,0},{255,255}}], title,
Circle[pts[[1]],r],Text[Style["Hb",  Medium],pts[[1]]+shift,align[pts[[1,2]],pts[[2,2]]]],
Circle[pts[[2]],r],Text[Style["HbO2",Medium],pts[[2]]+shift,align[pts[[2,2]],pts[[1,2]]]],
Circle[pts[[3]],r],Text[Style["Eumelanin",  Medium],pts[[3]]+shift,align[pts[[3,2]],pts[[4,2]]]],
Circle[pts[[4]],r],Text[Style["Pheomelanin",Medium],pts[[4]]+shift,align[pts[[4,2]],pts[[3,2]]]]},ImageSize->500]
]
];


Abs[pts[[1,2]]-pts[[2,2]]] < r


chromaticPlane[0.9,{{245,56,21},{251,51,8},{231,123,48},{239,119,31}},Frame->False]
