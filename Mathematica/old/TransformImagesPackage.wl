(* ::Package:: *)

(* ::Subsubsection:: *)
(*Init.*)


Clear[val,setLCaCb]
setLCaCb[\[Theta]_] := Module[{R, toLCaCb, fromLCaCb}, 
      toLCaCb = Function[{val}, "rrR" . val + {0, 0.5, 0.5}] /. {"rrR" -> N[nLCaCb[\[Theta]]]}; 
    fromLCaCb = Function[{val}, "iR" . ((val - {0, 0.5, 0.5}))] /. {"iR" -> inLCaCb[\[Theta]]};
 {toLCaCb, fromLCaCb}]


Clear[WOBOPathLCaCb]
WOBOPathLCaCb[lCaCb:{_,_,_},scale_:1,\[Theta]_]:=Module[{ordering,sca,a,b,c,toLCaCb, fromLCaCb,rgb},
{toLCaCb, fromLCaCb}=setLCaCb[\[Theta]];
rgb=fromLCaCb[lCaCb];
ordering = Ordering[rgb];
{a,b,c}=Part[rgb,ordering];
scale {
toLCaCb[{0,0,0}],
toLCaCb[ReplacePart[rgb-b,{ordering[[1]]->0,ordering[[2]]->0}]],
toLCaCb[(rgb-a)],
toLCaCb[(rgb+(1-c))],
toLCaCb[(ReplacePart[rgb+(1-b),{ordering[[3]]->1,ordering[[2]]->1}])],
toLCaCb[({1,1,1})]}
]


(* ::Subsubsection:: *)
(*Init : The Probability Function*)


Clear[setProbFun]
setProbFun[rules_]:=Module[{cd,\[Mu]d,sd,\[Sigma]d,pxl},
cd=("dstMax"/.rules)/2;
\[Mu]d={0.5,0.5,0.5};
sd=("dstMax"/.rules)  ("s"/.rules)/(("\[CapitalLambda]"/.rules)[[All,2]]-("\[CapitalLambda]"/.rules)[[All,1]]);
\[Sigma]d=("\[Sigma]"/.rules)/(("\[Lambda]"/.rules)[[All,2]]-("\[Lambda]"/.rules)[[All,1]]);
Quiet[{Function[{"pxl"},Chop["fun"]]/.{"pxl"->pxl,"fun"->Exp[-(pxl[[2]]-\[Mu]d[[2]])^2/(2( \[Sigma]d[[2]])^2)]  Exp[-(pxl[[3]]-\[Mu]d[[3]])^2/(2 (\[Sigma]d[[3]])^2)]},
Function[{"pxl"},Chop["fun"]]/.{"pxl"->pxl,"fun"->Exp[-(pxl[[2]]-cd[[2]])^2/(2( sd[[2]])^2)]  Exp[-(pxl[[3]]-cd[[3]])^2/(2 (sd[[3]])^2)]}},{Part::partd,Function::flpar}] ]


Clear[setProbFun]
setProbFun[rules_]:=Module[{dstMax,cd,\[Mu]d,sd,\[Sigma]d,pxl},
dstMax=("dstMax"/.rules);
cd=dstMax/2;
\[Mu]d={0.5,0.5,0.5};
sd=dstMax  ("s"/.rules)/(("\[CapitalLambda]"/.rules)[[All,2]]-("\[CapitalLambda]"/.rules)[[All,1]]);
\[Sigma]d=("\[Sigma]"/.rules)/(("\[Lambda]"/.rules)[[All,2]]-("\[Lambda]"/.rules)[[All,1]]);
Quiet[Function[{L,Ca,Cb},Evaluate["Chop"[Exp[-(Ca/dstMax[[2]]-\[Mu]d[[2]])^2/(2( \[Sigma]d[[2]])^2)]  Exp[-(Cb/dstMax[[3]]-\[Mu]d[[3]])^2/(2 (\[Sigma]d[[3]])^2)]]]]/.{"Chop"->Chop},{Part::partd,Function::flpar}] ]


(* ::Subsubsection:: *)
(*Init : The Unreliable Function*)


slack[x_,a_:0.1]:=Piecewise[{{(1-a)x,x<1/2},{(1+a) x,x>1/2},{x,True}}]



Options[setUnreliableFun]={qRange->True,Slack->0.1};
setUnreliableFun[rules_,sig_:1,OptionsPattern[]]:=Module[{\[Mu],\[Sigma],\[Theta],chMM,MMBO,MMWO,LWOBOLimits,CaWOBOLimits,CbWOBOLimits,scale,corners,path,BoPaths,WoPaths,MMBoPaths,MMWoPaths},
\[Mu]="\[Mu]"/.rules;
\[Sigma]="\[Sigma]"/.rules;
\[Theta]="\[Theta]"/.rules; \[Lambda]="\[Lambda]"/.rules;
chMM=Function[{list},({MapThread[Min,list],MapThread[Max,list]})];
(* corners = {\[Mu]+{0,-sig \[Sigma][[2]],-sig \[Sigma][[3]]},\[Mu]+{0,-sig \[Sigma][[2]],+sig \[Sigma][[3]]},\[Mu]+{0,+sig \[Sigma][[2]],-sig \[Sigma][[3]]},\[Mu]+{0,+sig \[Sigma][[2]],+sig \[Sigma][[3]]}}; *)
corners = {{\[Mu][[1]],\[Lambda][[2,1]],\[Lambda][[3,1]]},{\[Mu][[1]],\[Lambda][[2,2]],\[Lambda][[3,1]]},{\[Mu][[1]],\[Lambda][[2,1]],\[Lambda][[3,2]]},{\[Mu][[1]],\[Lambda][[2,2]],\[Lambda][[3,2]]}};
paths = Map[WOBOPathLCaCb[#,1,\[Theta]]&,corners];
BoPaths=paths[[All,1;;3]];
WoPaths=paths[[All,4;;6]];
MMBoPaths = Flatten[Map[Map[slack[#,OptionValue[Slack]]&,chMM[(#)],{2}]&,BoPaths],1];
MMWoPaths = Flatten[Map[Map[slack[#,OptionValue[Slack]]&,chMM[(#)],{2}]&,WoPaths],1];
MMBO=chMM[MMBoPaths];
MMWO=chMM[MMWoPaths];
LWOBOLimits={MMBO[[2,1]],MMWO[[1,1]]};
CaWOBOLimits={Min[{MMBO[[1,2]],MMWO[[1,2]]}],Max[{MMBO[[2,2]],MMWO[[2,2]]}]};
CbWOBOLimits={Min[{MMBO[[1,3]],MMWO[[1,3]]}],Max[{MMBO[[2,3]],MMWO[[2,3]]}]};
If[OptionValue[qRange], scale=("qRsRange"/.rules), scale={1,1,1}];
Function[{L,Ca,Cb},Evaluate[(
!(scale[[1]]  LWOBOLimits[[1]] < L  < scale[[1]]  LWOBOLimits[[2]]))&&
  scale[[2]] CaWOBOLimits[[1]] < Ca < scale[[2]] CaWOBOLimits[[2]]  &&
  scale[[3]] CbWOBOLimits[[1]] < Cb < scale[[3]] CbWOBOLimits[[2]]]]
]


(* ::Subsubsection:: *)
(*Init : The Partition Function*)


Options[setColorTargetFun]={qRange->True};
setColorTargetFun[rules_,sig_:1,OptionsPattern[]]:=Module[{ \[Mu], \[Sigma],\[Lambda], minorAxisEnds, majorAxisEnds,L,Ca,Cb,scale},
\[Mu]=("\[Mu]"/.rules); \[Sigma]=("\[Sigma]"/.rules);\[Lambda]="\[Lambda]"/.rules;
minorAxisEnds={{\[Mu][[1]],\[Mu][[2]],\[Lambda][[3,1]]},{\[Mu][[1]],\[Mu][[2]],\[Lambda][[3,2]]}};
majorAxisEnds={{\[Mu][[1]],\[Lambda][[2,1]],\[Mu][[3]]},{\[Mu][[1]],\[Lambda][[2,2]],\[Mu][[3]]}};
If[OptionValue[qRange], scale=("qRsRange"/.rules), scale={1,1,1}];
{Function[{L,Ca,Cb},Evaluate[scale[[2]] majorAxisEnds[[1,2]] < Ca < scale[[2]] majorAxisEnds[[2,2]]&& scale[[3]] minorAxisEnds[[1,3]] < Cb < scale[[3]] minorAxisEnds[[2,3]]]],
 Function[{L,Ca,Cb},Evaluate[(Ca/scale[[2]]-\[Mu][[2]])^2/((\[Lambda][[2,2]]-\[Lambda][[2,1]])/2)^2 + (Cb/scale[[3]]-\[Mu][[3]])^2/((\[Lambda][[3,2]]-\[Lambda][[3,1]])/2)^2<=1]]}
]


Clear[setPartitioningFun];
setPartitioningFun[rules_,sig_:1]:=Module[{ \[Mu], \[Sigma], \[Lambda], dstMax, disFun, minorAxisEnds, majorAxisEnds,L,Ca,Cb,CaQ,CbQ,scale,CaMin,CaMax,CbMin,CbMax},
\[Mu]=("\[Mu]"/.rules); \[Sigma]=("\[Sigma]"/.rules);\[Lambda]="\[Lambda]"/.rules;
dstMax=("dstMax"/.rules);
disFun="disFun"/.rules;
minorAxisEnds=Evaluate[{{\[Mu][[1]],\[Mu][[2]],\[Lambda][[3,1]]},{\[Mu][[1]],\[Mu][[2]],\[Lambda][[3,2]]}}];
majorAxisEnds={{\[Mu][[1]],\[Lambda][[2,1]],\[Mu][[3]]},{\[Mu][[1]],\[Lambda][[2,2]],\[Mu][[3]]}};
scale=("qRsRange"/.rules);
Function[{L,Ca,Cb},
Evaluate[
CaMin=0;CaMax=dstMax[[2]];
CbMin=0;CbMax=dstMax[[3]];
CaQ={Ca < scale[[2]] majorAxisEnds[[1,2]] , Ca < scale[[2]] majorAxisEnds[[2,2]]};
CbQ={Cb < scale[[3]] minorAxisEnds[[1,3]] , Cb < scale[[3]] minorAxisEnds[[2,3]]};
If["CaQl"&&"CaQh",
(*Low Ca*)
If["CbQl"&&"CbQh",
(*Low Cb*)
{Round[N["disL"]],"CaMin","CbMin"},
If[!"CbQl"&&"CbQh",
(*Distribute Cb*)
{Round[N["disL"]],"CaMin","\[Mu]3"},
If[!"CbQl"&&!"CbQh",
(*High Cb*)
{Round[N["disL"]],"CaMin","CbMax"}
]]]
,
If[!"CaQl"&&"CaQh",
(*Distribute Ca*)
If["CbQl"&&"CbQh",
(*Low Cb*)
{Round[N["disL"]],"\[Mu]2","CbMin"},
If[!"CbQl"&&"CbQh",
(*Distribute Cb*)
{Round[N["disL"]],Round[N["disCa"]],Round[N["disCb"]]},
If[!"CbQl"&&!"CbQh",
(*High Cb*)
{Round[N["disL"]],"\[Mu]2","CbMax"}
]]]
,
If[!"CaQl"&&!"CaQh",
(*High Ca*)
If["CbQl"&&"CbQh",
(*Low Cb*)
{Round[N["disL"]],"CaMax","CbMin"},
If[!"CbQl"&&"CbQh",
(*Distribute Cb*)
{Round[N["disL"]],"CaMax","\[Mu]3"},
If[!"CbQl"&&!"CbQh",
(*High Cb*)
{Round[N["disL"]],"CaMax","CbMax"}
]]]
]]]/.{
"CaQl"-> Ca < Evaluate[scale[[2]] majorAxisEnds[[1,2]]] ,"CaQh"-> Ca < Evaluate[scale[[2]] majorAxisEnds[[2,2]]],
"CbQl"-> Cb < Evaluate[scale[[3]] minorAxisEnds[[1,3]]] ,"CbQh"-> Cb < Evaluate[scale[[3]] minorAxisEnds[[2,3]]],
"CaMin"-> 0,"CaMax"-> dstMax[[2]],
"CbMin"-> 0,"CbMax"-> dstMax[[3]],"\[Mu]2"->Round[N[dstMax[[2]] \[Mu][[2]]]],"\[Mu]3"->Round[N[dstMax[[3]] \[Mu][[3]]]],"disL"->disFun[[1]][L],"disCa"->disFun[[2]][Ca],"disCb"->disFun[[3]][Cb]}]]
]


Clear[setDistroFun];
setDistroFun[rules_]:=Module[{ disFun},
disFun="disFun"/.rules;
Function[{L,Ca,Cb},
Evaluate[
{Round[N["disL"]],Round[N["disCa"]],Round[N["disCb"]]}/.{
"disL"->disFun[[1]][L],"disCa"->disFun[[2]][Ca],"disCb"->disFun[[3]][Cb]}]]
]


showColorTargetFun[rules_,sig_:1]:=Module[{color, \[Mu],\[Sigma],minorAxisEnds,majorAxisEnds,txt,rec},
\[Mu]=("\[Mu]"/.rules);
\[Sigma]=("\[Sigma]"/.rules);
color=("LCaCbColor"/.rules);
minorAxisEnds={\[Mu]-{0,0,sig \[Sigma][[3]]},\[Mu]+{0,0,sig \[Sigma][[3]]}};
majorAxisEnds={\[Mu]-{0,sig \[Sigma][[2]],0},\[Mu]+{0,sig \[Sigma][[2]],0}};
txt={
 {Opacity[1],Black,
  Inset[MatrixForm[{"\[Tilde]",               0,                0}],{ majorAxisEnds[[1,2]]/2,                        minorAxisEnds[[1,3]]/2 }],
  Inset[MatrixForm[{"\[Tilde]",Subscript["\[Mu]",2],                0}],{(majorAxisEnds[[1,2]]+majorAxisEnds[[2,2]])/2,  minorAxisEnds[[1,3]]/2}],
  Inset[MatrixForm[{"\[Tilde]",               1,                0}],{(1+majorAxisEnds[[2,2]])/2,                     minorAxisEnds[[1,3]]/2}]},
{ Inset[MatrixForm[{"\[Tilde]",               0, Subscript["\[Mu]",3]}],{majorAxisEnds[[1,2]]/2,                        (minorAxisEnds[[1,3]]+minorAxisEnds[[2,3]])/2}],
  Inset[MatrixForm[{"\[Tilde]",             "\[Tilde]",              "\[Tilde]"}],{(majorAxisEnds[[1,2]]+majorAxisEnds[[2,2]])/2, (minorAxisEnds[[1,3]]+minorAxisEnds[[2,3]])/2}],
  Inset[MatrixForm[{"\[Tilde]",               1, Subscript["\[Mu]",3]}],{(1+majorAxisEnds[[2,2]])/2,                    (minorAxisEnds[[1,3]]+minorAxisEnds[[2,3]])/2}]},
{ Inset[MatrixForm[{"\[Tilde]",               0,                1}],{majorAxisEnds[[1,2]]/2,                        (1+minorAxisEnds[[2,3]])/2}],
  Inset[MatrixForm[{"\[Tilde]",Subscript["\[Mu]",2],                1}],{(majorAxisEnds[[1,2]]+majorAxisEnds[[2,2]])/2, (1+minorAxisEnds[[2,3]])/2}],
  Inset[MatrixForm[{"\[Tilde]",               1,                1}],{(1+majorAxisEnds[[2,2]])/2,                    (1+minorAxisEnds[[2,3]])/2}]}};
rec={EdgeForm[Black],FaceForm[],Ellipsoid[\[Mu][[2;;3]],{(majorAxisEnds[[2,2]]-majorAxisEnds[[1,2]])/2,(minorAxisEnds[[2,3]]-minorAxisEnds[[1,3]])/2}],
Opacity[0.3],
FaceForm[color[0.65,(majorAxisEnds[[1,2]]+majorAxisEnds[[2,2]])/2,0]],
Rectangle[{majorAxisEnds[[1,2]],0},{majorAxisEnds[[2,2]],minorAxisEnds[[1,3]]}],
color[0.65,(majorAxisEnds[[1,2]]+majorAxisEnds[[2,2]])/2,1],
Rectangle[{majorAxisEnds[[1,2]],minorAxisEnds[[2,3]]},{majorAxisEnds[[2,2]],1}],
color[0.65,0,(minorAxisEnds[[1,3]]+minorAxisEnds[[2,3]])/2],
Rectangle[{0,minorAxisEnds[[1,3]]},{majorAxisEnds[[1,2]],minorAxisEnds[[2,3]]}],
color[0.65,1,(minorAxisEnds[[1,3]]+minorAxisEnds[[2,3]])/2],
Rectangle[{majorAxisEnds[[2,2]],minorAxisEnds[[1,3]]},{1,minorAxisEnds[[2,3]]}],
color[0.65,\[Mu][[2]],\[Mu][[3]]],
Rectangle[{majorAxisEnds[[1,2]],minorAxisEnds[[1,3]]},{majorAxisEnds[[2,2]],minorAxisEnds[[2,3]]}],
color[0.65,0,1],
Rectangle[{0,minorAxisEnds[[2,3]]},{majorAxisEnds[[1,2]],1}],
color[0.65,1,1],
Rectangle[{majorAxisEnds[[2,2]],minorAxisEnds[[2,3]]},{1,1}],
color[0.65,0,0],
Rectangle[{0,0},{majorAxisEnds[[1,2]],minorAxisEnds[[1,3]]}],
color[0.65,1,0],
Rectangle[{majorAxisEnds[[2,2]],0},{1,minorAxisEnds[[1,3]]}]
};
Graphics[{rec,txt},Frame->True,FrameLabel->{{"Cb",None},{"Ca",None}},FrameTicks->{
{{0,-Subscript["qRange",2]},{1,Subscript["qRange",2]},{\[Mu][[2]]-sig \[Sigma][[2]],Subscript["\[CapitalLambda]q",1]},{\[Mu][[2]],"\[Mu]"},{\[Mu][[2]]+sig \[Sigma][[2]],Subscript["\[CapitalLambda]q",2]}},
{{0,-Subscript["qRange",3]},{1,Subscript["qRange",3]},{\[Mu][[3]]-sig \[Sigma][[3]],Subscript["\[CapitalLambda]q",1]},{\[Mu][[3]],"\[Mu]"},{\[Mu][[3]]+sig \[Sigma][[3]],Subscript["\[CapitalLambda]q",2]}} }]
]



(* ::Subsubsection:: *)
(*Init : The Classifier Function*)


regionFun = Function[{color,unreliable},FromDigits[Boole[{color,Xor[color,unreliable]}],2]];


Clear[RegionClassifier]
Options[RegionClassifier]={qRange->True};
RegionClassifier[rules_,sig_:1,opts:OptionsPattern[]]:=Module[{unreliableFun,colorTargetSquare,colorTargetElliptical},
unreliableFun=setUnreliableFun[rules,sig,FilterRules[{opts},Options[setUnreliableFun]]];
{colorTargetSquare,colorTargetElliptical} = setColorTargetFun[rules,sig,FilterRules[{opts},Options[setColorTargetFun]]];
Function[{L,Ca,Cb},Evaluate[regionFun[colorTargetSquare[L,Ca,Cb],unreliableFun[L,Ca,Cb]]]]
]


(* ::Subsubsection:: *)
(*Init : The Channel Image Function*)


findSpectrum[start_,end_,div_]:=Module[{delta},
delta=(end-start)/(div);
Table[start+i delta,{i,0,div}]
]


Clear[ChannelImage]
ChannelImage[img_,chn_,colorRules_,cRng:{_,_}:{Null,Null}]:=Module[{toLCaCb, fromLCaCb,\[Mu],dstMin,dstMax,CStart,CEnd,pts,min,max,rng,rgbPts,ticks,wt,ht,chanColorAxis,rules,CMin,CMax},
{toLCaCb, fromLCaCb}=setLCaCb["\[Theta]"]/.colorRules;
\[Mu]=("\[Mu]"/.colorRules);
If[TrueQ[cRng[[1]]==Null], CMin=0, CMin=cRng[[1]]]; 
If[TrueQ[cRng[[2]]==Null], 
  dstMax="dstMax"/.colorRules; CMax=dstMax[[chn]],
  CMax=cRng[[2]]];
CStart=ReplacePart[\[Mu],chn->0];
CEnd=ReplacePart[\[Mu],chn->1];
(* pts=findSpectrum[fromLCaCb[CStart],fromLCaCb[CEnd],CMax-CMin]; *)
pts=pointsOnPath[{fromLCaCb[CStart],fromLCaCb[CEnd]},CMax-CMin];
min={Min[pts[[All,1]]],Min[pts[[All,2]]],Min[pts[[All,3]]]};
max={Max[pts[[All,1]]],Max[pts[[All,2]]],Max[pts[[All,3]]]};
rng=max-min;
rgbPts=Map[((#-min)/rng)&,pts];
ticks=Flatten[{CMin,Table[Round[N[i]],{i,CMin,CMax,(CMax-CMin)/8}],CMax}];
{ht,wt}=Dimensions[img][[1;;2]];
chanColorAxis=Graphics[{Rectangle[{0,0},{wt,ht}],Table[{RGBColor[rgbPts[[i-CMin+1]]],Rectangle[{wt,(i-CMin)ht/((CMax-CMin)+1)},{wt+ht/10,(i-CMin+1)ht/((CMax-CMin)+1)}],
Black,If[MemberQ[ticks,i],Text[i,{wt+ht/9,(i-CMin+0.5)ht/((CMax-CMin)+1)},{-1,0}]]},{i,CMin,CMax}]}];
rules=Table[i->RGBColor[rgbPts[[i-CMin+1]]],{i,CMin,CMax}];
Show[{chanColorAxis,Image[img[[All,All,chn]]/.rules]},ImageSize->{wt+ht/5,ht}]
]


(* ::Subsubsection:: *)
(*Init : Show the Image in {x,y} coords*)


imageGraphics[img_Image,rotM_:{{1,0},{0,1}}]:=Module[{w,h},
{h,w}=Dimensions[ImageData[img]][[1;;2]];
Graphics[{Texture[img],Polygon[Transpose[rotM . Transpose[{{1,1},{1,w},{h,w},{h,1}}]],VertexTextureCoordinates->{{0,1},{1,1},{1,0},{0,0}}]}]
]
imageGraphics[img_List,rotM_:{{1,0},{0,1}}]:=Module[{w,h},
{h,w}=Dimensions[img][[1;;2]];
Graphics[{Texture[Image[img]],Polygon[Transpose[rotM . Transpose[{{1,1},{1,w},{h,w},{h,1}}]],VertexTextureCoordinates->{{0,1},{1,1},{1,0},{0,0}}]}]
]


(* ::Subsubsection:: *)
(*Init: medianMean average function*)


Clear[medianMean]
medianMean[pnts_,frac_:0.3]:=Module[{medianPos,mean,srtd},
srtd = Sort[pnts];
medianPos={Round[(Length[srtd]-1)(1-frac)/2 +1],Round[(Length[srtd]-1)(1+frac)/2 +1]};
mean=Total[srtd[[medianPos[[1]];;medianPos[[2]]]]]/(medianPos[[2]]-medianPos[[1]]+1);
{mean, Max[{mean-srtd[[medianPos[[1]]]],srtd[[medianPos[[2]]]] - mean}]}
]


(* ::Subsubsection:: *)
(*Init: Eliptical fit to the tip*)


Clear[IsEllipse]
IsEllipse[Axx_,Axy_,Ayy_,Ax_,Ay_,A0_]:=Module[{aa,bb,cc},
aa = Axy^2-4 Axx Ayy;
bb=Ax Axy Ay-Axx Ay^2-Ax^2 Ayy;
cc=Axy^2/(4 Axx);
(Axx < 0 &&  Ayy < cc && A0 > bb/aa)||( Axx > 0 &&  Ayy > cc && A0 < bb/aa)
]


EllipsePropertiesFromCoeffs[Axx_,Axy_,Ayy_,Ax_,Ay_,A0_]:=Module[{x0,y0,a,b,\[Theta],u1,u2,l1,l2,l3,p1,p2},

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


Clear[EllipseCoeffsFromProperties]
EllipseCoeffsFromProperties[{{x0_,y0_},{a_,b_},\[Theta]_}]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0},
Axx=b^2 Cos[\[Theta]]^2+a^2 Sin[\[Theta]]^2;
Axy=-2 a^2 Cos[\[Theta]] Sin[\[Theta]]+2 b^2 Cos[\[Theta]] Sin[\[Theta]];
Ayy=a^2 Cos[\[Theta]]^2+b^2 Sin[\[Theta]]^2;
Ax=-2 b^2 x0 Cos[\[Theta]]^2+2 a^2 y0 Cos[\[Theta]] Sin[\[Theta]]-2 b^2 y0 Cos[\[Theta]] Sin[\[Theta]]-2 a^2 x0 Sin[\[Theta]]^2;
Ay=-2 a^2 y0 Cos[\[Theta]]^2+2 a^2 x0 Cos[\[Theta]] Sin[\[Theta]]-2 b^2 x0 Cos[\[Theta]] Sin[\[Theta]]-2 b^2 y0 Sin[\[Theta]]^2;
A0=-a^2 b^2+b^2 x0^2 Cos[\[Theta]]^2+a^2 y0^2 Cos[\[Theta]]^2-2 a^2 x0 y0 Cos[\[Theta]] Sin[\[Theta]]+2 b^2 x0 y0 Cos[\[Theta]] Sin[\[Theta]]+a^2 x0^2 Sin[\[Theta]]^2+b^2 y0^2 Sin[\[Theta]]^2;
{Axx,Axy,Ayy,Ax,Ay,A0}
]


EllipseXFunFromProperties[{{x0_,y0_},{a_,b_},\[Theta]_}]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0},
{Axx,Axy,Ayy,Ax,Ay,A0}=EllipseCoeffsFromProperties[{{x0,y0},{a,b},\[Theta]}];
Function[{x},Evaluate[{(-Ay-Axy x+Sqrt[(Ay+Axy x)^2-4 Ayy (A0+Ax x+Axx x^2)])/(2 Ayy),(-Ay-Axy x-Sqrt[(Ay+Axy x)^2-4 Ayy (A0+Ax x+Axx x^2)])/(2 Ayy)}]]
]


EllipseYFunFromProperties[{{x0_,y0_},{a_,b_},\[Theta]_}]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0},
{Axx,Axy,Ayy,Ax,Ay,A0}=EllipseCoeffsFromProperties[{{x0,y0},{a,b},\[Theta]}];
Function[{y},Evaluate[{(-Ax-Axy y-Sqrt[(Ax+Axy y)^2-4 Axx (A0+Ay y+Ayy y^2)])/(2 Axx),(-Ax-Axy y+Sqrt[(Ax+Axy y)^2-4 Axx (A0+Ay y+Ayy y^2)])/(2 Axx)}]]
]


getModelAxis[model_]:=Module[{tt1x,tt2x,tb1x,tb2x,tt1y,tt2y,tb1y,tb2y},
{{{tt1x,tt1y},{tt2x,tt2y}},{{tb1x,tb1y},{tb2x,tb2y}}}=model[[1]];
ArcTan[1/2 (-tb1x-tt1x)+(tb2x+tt2x)/2,1/2 (-tb1y-tt1y)+(tb2y+tt2y)/2]
]


Clear[modelToPoints]
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


Clear[EllipseFitCoeffs]
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


EllipseFitCoeffs[points_,"Direct"]:=Module[{c,D1,D2,S1,S2,S3,eVal,eVec,pos,T,M,cond,A,A1,A4,A5,A6,Axx,Axy,Ayy,Ax,Ay,A0,x0,y0,a,b,\[Theta]},
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


Clear[EllipseFit]
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


EllipseFit[points_,"Direct"]:=Module[{Axx,Axy,Ayy,Ax,Ay,A0,x0,y0,a,b,\[Theta]},
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


Clear[ellipseThetaSpacings]
ellipseThetaSpacings[{x0_,y0_},{a_,b_},\[Theta]_,n_]:=Module[{perim,\[Phi],\[Delta]\[Phi],pnt,t},
perim=N[ArcLength[{a Cos[t],b Sin[t]},{t,0,2Pi}]];
\[Delta]\[Phi] = Function[{\[Phi]},Evaluate[(perim/n)/Sqrt[(a^2 Cos[\[Phi]]^2 + b^2 Sin[\[Phi]]^2)]]];
\[Phi]=0;
pnt=Table[
\[Phi]=\[Phi]+(\[Delta]\[Phi][\[Phi]]+\[Delta]\[Phi][\[Phi]+\[Delta]\[Phi][\[Phi]]])/2,
{i,1,n}]+\[Theta];
Sort[Map[Mod[#,2Pi]&,pnt]]
]


Clear[EllipseFun];
EllipseFun[{x0_,y0_},{a_,b_},theta_]:=Module[{r},
r=Function[{\[Theta]},Evaluate[a b /Sqrt[(b Cos[\[Theta]])^2 +(a Sin[\[Theta]])^2 ]]];
Function[{\[Theta]},Evaluate[{x0,y0}+RotationMatrix[theta].( r[\[Theta]] {Cos[\[Theta]],Sin[\[Theta]]})]]
]


Clear[randomEllipse];
randomEllipse[{x0_,y0_},{a_,b_},\[Theta]_,n_,var_:1/40]:=Module[{fun,dFun},
fun=EllipseFun[{x0,y0},{a,b},\[Theta]];
dFun=EllipseFun[{0,0},{a,b},\[Theta]];
Table[
fun[t]+(dFun[t]/Norm[dFun[t]]) {RandomVariate[NormalDistribution[0,var a ]],RandomVariate[NormalDistribution[0,var b ]]}
,{t,ellipseThetaSpacings[{x0,y0},{a,b},\[Theta],n]}]
]


EllipseNormal[{x0_,y0_},{a_,b_},\[Theta]_,\[Phi]_]:=Module[{t},
t=\[Phi]-\[Theta];
RotationMatrix[\[Theta]].{-((b Cos[t])/Sqrt[b^2 Cos[t]^2+a^2 Sin[t]^2]),-((a Sin[t])/Sqrt[b^2 Cos[t]^2+a^2 Sin[t]^2])}]


(* ::Subsubsection:: *)
(*Set Scales : init*)


factorsToFactors[factors_]:=Module[{powers},
powers=Map[Table[#[[1]]^i,{i,0,#[[2]]}]&,factors];
Sort[Flatten[Outer[Times,Sequence@@(Reverse[powers])]]]
]


Clear[findMediumScale];
findMediumScale[target_,num_Integer]:=Module[{scales,i},
scales=factorsToFactors[FactorInteger[num]];
findMediumScale[target,scales]
]
findMediumScale[target_,scales_List]:=Module[{pos,i},
i=0;
While[i < Length[scales] && target-scales[[i+1]]>=  0 , i++;];
scales[[i]]
]



CommonFactors[nums_]:=Module[{factors,commonBase},
factors=FactorInteger[nums];
commonBase=Intersection[Sequence@@factors[[All,All,1]]];
Table[Sort[Extract[factors,Position[factors,{i,_}]]][[1]],{i,commonBase}]
]


(* ::Subsubsection:: *)
(*Calc New Mean : Init*)


calcNewMean[img_,patch_,rules_]:=Module[{imgData,imgDataSkin,imgLCaCb,\[Mu]Skin},
imgData=ImageData[img,"Byte"];
imgDataSkin=imgData[[patch[[1,1]];;patch[[1,2]],patch[[2,1]];;patch[[2,2]]]];
imgLCaCb=processImage[imgDataSkin,{},{},rules,Unit->True];
\[Mu]Skin=N[Total[imgLCaCb,2]/Times@@(Dimensions[imgLCaCb][[1;;2]])];
colorSpaceParams[ ("\[Sigma]"/.rules),\[Mu]Skin,("\[Theta]"/.rules),8,{{"sMin","sMax"},{"dMin","dMax"}}/.rules,Unit->True,G->False]
]


(* ::Subsubsection:: *)
(*Image Component Analysis : Init*)


frameOrientation[imgClassified_,dp_]:=Module[{w,h,edgeTotal},
{h,w}=Dimensions[imgClassified];
edgeTotal=
{Total[imgClassified[[1;;dp,All]]/.{1->0},2]/(dp w),
Total[imgClassified[[h-dp;;h,All]]/.{1->0},2]/(dp w),
Total[imgClassified[[All,1;;dp]]/.{1->0},2]/(dp h),
Total[imgClassified[[All,w-dp;;w]]/.{1->0},2]/(dp h)
};
Extract[{{1,0},{-1,0},{0,1},{0,-1}},Position[edgeTotal,Max[edgeTotal]]][[1]]
]


findStartingPoint[imgClassified_,dp_]:=Module[{w,h,avg,imgClass,direction,transposeQ,transF,startEnd,counting,pass,se,runLength,start,pnts,startPnt},
direction=frameOrientation[imgClassified, dp];
transposeQ=TrueQ[direction[[1]]!= 0];
transF=If[transposeQ, Function[{list},Transpose[list]], Function[{list},list]];
imgClass=imgClassified/.{1->0};
{h,w}=Dimensions[imgClass];
avg=Map[(Total[#]/dp)&,transF[imgClass[[Sequence@@(direction/.{1->1;;dp,-1-> -dp;;-1,0->All})]]]];
startEnd={};
counting=False;
Do[
pass=avg[[wh]]>2;
If[Not[counting]&&pass,counting=True; se=wh];
If[counting&&Not[pass],counting=False; AppendTo[startEnd,{se,wh}]];
,{wh,1,Length[avg]}];
runLength=startEnd[[All,2]]-startEnd[[All,1]];
start=Extract[startEnd,Position[runLength,Max[runLength]]][[1]];
pnts={(direction/.{{0,-1}->{start[[1]],w},{-1,0}->{h,start[[1]]},{0,1}->{start[[1]],0},{1,0}->{0,start[[1]]}}),
(direction/.{{0,-1}->{start[[2]],w},{-1,0}->{h,start[[2]]},{0,1}->{start[[2]],0},{1,0}->{0,start[[2]]}})};
startPnt=direction/.{{0,-1}->{Total[start]/2,w},{-1,0}->{h,Total[start]/2},{0,1}->{Total[start]/2,1},{1,0}->{1,Total[start]/2}}
]


Clear[run,reach,runReach]
run[img_,strt_,dir_,tol:{_,_}]:=Module[{runQ,countQ,indx,i,out,w,h},
{h,w}=Dimensions[img][[1;;2]];
runQ=True; countQ=True;
indx=strt; out=indx; i=0;
While[runQ,i=i+1;indx=Round[strt+i dir];
If[indx[[1]]>=1 && indx[[1]]<= h && indx[[2]]>=1 && indx[[2]]<= w,
  countQ = img[[indx[[1]],indx[[2]]]]>= tol[[1]];
  runQ   = img[[indx[[1]],indx[[2]]]]>= tol[[2]];
 If[countQ, out=indx];, 
  countQ=False; runQ=False; ]
];
out];

reach[img_,strt_,dir_,tol:{_,_}]:=Module[{dirP},
dirP=RotationMatrix[Pi/2] . dir;
{run[img,strt,dirP,tol],run[img,strt,-dirP,tol]}
];

runReach[img_,strt_,dir_,tol:{_,_},MidQ_:True,EdgeQ_:True,RunQ_:False]:=Module[{out,midOut,runOut,points,runQ,mid,runPts},
out={};
midOut={strt};
runOut={run[img,strt,dir,tol]};
points=reach[img,runOut[[1]],dir,tol];
AppendTo[out,points];
runQ=True;
While[Max[Abs[points[[1]]-points[[2]]]]>2&&runQ,
mid=Round[(points[[1]]+points[[2]])/2];
AppendTo[midOut,mid];
runPts=run[img,mid,dir,tol];
AppendTo[runOut,runPts];
runQ=Max[Abs[mid-runPts]]>0;
If[runQ,
points=reach[img,runPts,dir,tol];
AppendTo[out,points];
]
];
(* Flatten[out,1] *)
{If[MidQ,midOut],If[EdgeQ,out],If[RunQ,runOut]}/.Null->Sequence[]
]


pointsToEquation[pntA_,pntB_]:=Module[{},
Function[{x,y},Evaluate[
(pntB[[1]]-pntA[[1]])(y-pntA[[2]])-(pntB[[2]]-pntA[[2]])(x-pntA[[1]])]]
]
pointsToEquationX[pntA_,pntB_]:=Module[{m,c,x},
m = (pntB[[2]]-pntA[[2]])/(pntB[[1]]-pntA[[1]]);
c = pntA[[2]]- m pntA[[1]];
Function[{x},Evaluate[m x + c]]
]
pointsToEquationY[pntA_,pntB_]:=Module[{m,c,x},
pointsToEquationX[Reverse[pntA],Reverse[pntB]]
]


Clear[perpDistToline]

perpDistToline[fun_Function, pnt:{_,_}] := Module[{f, g, a, b, m, c, d}, 
a=pnt[[1]]; b=pnt[[2]];
c = fun[0]; 
m = fun[1] - c; 
f[x_, mm_, cc_] := mm*x + cc; 
g[x_, mm_, aa_, bb_] := bb - (1/mm)*(x - aa); 
   {(m a + c - b)/Sqrt[1 + m^2], Line[{{a, b}, {(a + b m - c m)/(1 + m^2), g[(a + b m - c m)/(1 + m^2), m, a, b]}}]}
 ]
perpDistToline[line:{{_,_},{_,_}}, pnt:{_,_}] := Module[{f, g, a, b, c, lineF, perpVec, dist}, 
lineF=pointsToEquation[line[[1]],line[[2]]];
c=lineF[0,0]; a=lineF[1,0]-c; b=lineF[0,1]-c;
perpVec={a,b}/Sqrt[a^2+b^2]; 
dist=((line[[2,2]]-line[[1,2]]) pnt[[1]] - (line[[2,1]]-line[[1,1]] )pnt[[2]]+line[[2,1]] line[[1,2]] - line[[2,2]] line[[1,1]] )/Sqrt[(line[[2,2]]-line[[1,2]])^2 + (line[[2,1]]-line[[1,1]])^2];
   {Abs[dist], Line[{pnt, pnt +dist perpVec}]}
 ]
perpDistToline[fun_, pnt:{_,_},limits:{{_,_},{_,_}},limitQ:{_,_}:{True,True}] := Module[{xLims,yLims,dist,line}, 
xLims=Sort[{limits[[1,1]],limits[[2,1]]}];
yLims=Sort[{limits[[1,2]],limits[[2,2]]}];
{dist,line} = perpDistToline[fun, pnt];
If[If[limitQ[[1]],(xLims[[1]]<=line[[1,2,1]]<=xLims[[2]]),True]&&If[limitQ[[2]],(yLims[[1]]<=line[[1,2,2]]<=yLims[[2]]),True],
{dist,line},
{0,Point[pnt]}
 ]
]
perpDistToline[fun_, pnt_List] := Module[{dLine}, 
dLine=Map[perpDistToline[fun, #]&,pnt];
{dLine[[All,1]],dLine[[All,2]]}
 ]
perpDistToline[fun_, pnt_List, limits:{{_,_},{_,_}},limitQ:{_,_}:{True,True}] := Module[{dLine, pos}, 
dLine=Map[perpDistToline[fun, #,limits, limitQ]&,pnt];
pos=Position[dLine, {Except[0],_},{1}];
dLine = dLine /. {{0,_}->Sequence[]};
{dLine[[All,1]],dLine[[All,2]],pos}
 ]


intersectionOfLines[{{Ax_, Ay_}, {Bx_, By_}}, {{AAx_, AAy_}, {BBx_, BBy_}}] := 
  Module[{x, y}, 
    y = (BBy*((-Ay)*Bx + AAx*(Ay - By) + Ax*By) + AAy*(Ay*(-BBx + Bx) + (-Ax + BBx)*By))/
          ((-Ay)*BBx + Ax*BBy - BBy*Bx + AAy*(-Ax + Bx) + AAx*(Ay - By) + BBx*By); 
    x = (AAy*BBx - AAx*BBy + AAx*y - BBx*y)/(AAy - BBy); 
{x, y}
]


Clear[distanceOnLine]
distanceOnLine[line_,d_]:=Module[{len,t,i,vec},
len=Table[v=(line[[i+1]]-line[[i]]);Sqrt[v.v],{i,1,Length[line]-1}];
t=0;i=1;
While[t+len[[i]]<d,t=t+len[[i]];i++];
vec=(line[[i+1]]-line[[i]])/Norm[(line[[i+1]]-line[[i]])];
line[[i]] + vec (d-t)
]


perpendicularProject[path_,w_List]:=Module[{nSeg,\[Theta],d},
nSeg=Length[path]-1;
\[Theta] = Table[vec=(path[[i+1]]-path[[i]]);ArcTan[vec[[2]]/vec[[1]] ]+Pi/2,{i,1,nSeg}];
d = Table[w[[i]] { Cos[\[Theta][[i]]],Sin[\[Theta][[i]]]} ,{i,1,nSeg}];
Table[{path[[i]]+d[[i]],path[[i+1]]+d[[i]]},{i,1,nSeg}]
]

Clear[sausageProject]
sausageProject[path_,w_List]:=Module[{\[Theta],\[Theta]t,d,vec,interX,projectedPts},
nSeg=Length[path]-1;
\[Theta] = Table[vec=(path[[i+1]]-path[[i]]);ArcTan[vec[[2]]/vec[[1]] ]+Pi/2,{i,1,nSeg}];
projectedPts=perpendicularProject[path,w];
interX = Table[intersectionOfLines[projectedPts[[i]],projectedPts[[i+1]]],{i,1,nSeg-1}];
interQ = Table[lims={Sort[N[{projectedPts[[i,2,1]],projectedPts[[i+1,1,1]]}]],Sort[N[{projectedPts[[i,2,2]],projectedPts[[i+1,1,2]]}]]};lims[[1,1]]<interX[[i,1]]<lims[[1,2]] && lims[[2,1]]<interX[[i,2]]<lims[[2,2]],{i,1,nSeg-1}];
\[Theta]t = Table[(\[Theta][[i]]+\[Theta][[i+1]])/2 ,{i,1,nSeg-1}]; 
dt = Table[{ Cos[\[Theta]t[[i]]],Sin[\[Theta]t[[i]]]} ,{i,1,nSeg-1}];
interXX = Table[If[interQ[[i]],
  interX[[i]],
  {path[[i+1]] +  (w[[i]]/Cos[\[Theta]t[[i]]-\[Theta][[i]]]) dt[[i]], path[[i+1]] + (w[[i]]+w[[i+1]])/2 dt[[i]], path[[i+1]] + (w[[i+1]]/Cos[\[Theta]t[[i]]-\[Theta][[i+1]]]) dt[[i]]} ],{i,1,nSeg-1}];
{projectedPts[[1,1]],Sequence@@interXX,projectedPts[[-1,2]]}
]
sausageProject[path_,w_]:=Module[{\[Theta],\[Theta]t,d,vec},
\[Theta] = Table[vec=(path[[i+1]]-path[[i]]);ArcTan[vec[[2]]/vec[[1]] ],{i,1,Length[path]-1}];
\[Theta]t = Table[(\[Theta][[i]]+\[Theta][[i+1]])/2+Pi/2 ,{i,1,Length[\[Theta]]-1}]; AppendTo[\[Theta]t,\[Theta][[-1]]+Pi/2];PrependTo[\[Theta]t,\[Theta][[1]]+Pi/2];
d = Table[w/2 { Cos[\[Theta]t[[i]]],Sin[\[Theta]t[[i]]]} ,{i,1,Length[\[Theta]t]}];
path+d
]
sausageLine[path_,color_]:=Module[{first, second, rLines, pLines},
first=Function[{pnt},If[Length[pnt]>=3,pnt[[1]],pnt]];
second=Function[{pnt},If[Length[pnt]>=3,pnt[[3]],pnt]];
rLines=Table[{color[[i]],Line[{second[path[[i]]],first[path[[i+1]]]}]},{i,1,Length[path]-1}];
pLines=Table[If[Length[path[[i]]]>=3,{color[[i-1]],Line[{path[[i,1]],path[[i,2]]}],color[[i]],Line[{path[[i,2]],path[[i,3]]}]} ,{} ],{i,1,Length[path]-1}];
{rLines,pLines}
]


Clear[toImgCoords]
toImgCoords[img_Image]:=toImgCoords[ImageData[img]];
toImgCoords[img_List]:=Module[{w,h},
{h,w}=Dimensions[img][[1;;2]];
Function[{pnt},Abs[(Reverse[pnt]-{0,hh})]]/.hh-> h
];


Clear[fromImgCoords]
fromImgCoords[img_Image]:=fromImgCoords[ImageData[img]];
fromImgCoords[img_List]:=Module[{w,h},
{h,w}=Dimensions[img][[1;;2]];
Function[{pnt},{pnt[[2]],hh-pnt[[1]]}]/.hh-> h
];


(* ::Subsection:: *)
(*Find Path to Tip : Init*)


Clear[run,reach,runReach]
run[img_,strt_,dir_,tol:{_,_}]:=Module[{runQ,countQ,indx,i,out,w,h},
{h,w}=Dimensions[img][[1;;2]];
runQ=True; countQ=True;
indx=strt; out=indx; i=0;
While[runQ,i=i+1;indx=Round[strt+i dir];
If[indx[[1]]>=1 && indx[[1]]<= h && indx[[2]]>=1 && indx[[2]]<= w,
  countQ = img[[indx[[1]],indx[[2]]]]>= tol[[1]];
  runQ   = img[[indx[[1]],indx[[2]]]]>= tol[[2]];
 If[countQ, out=indx];, 
  countQ=False; runQ=False; ]
];
out];

reach[img_,strt_,dir_,tol:{_,_}]:=Module[{dirP},
dirP=RotationMatrix[Pi/2] . dir;
{run[img,strt,dirP,tol],run[img,strt,-dirP,tol]}
];

runReach[img_,strt_,dir_,tol:{_,_},MidQ_:True,EdgeQ_:True,RunQ_:False]:=Module[{out,midOut,runOut,points,runQ,mid,runPts},
out={};
midOut={strt};
runOut={run[img,strt,dir,tol]};
points=reach[img,runOut[[1]],dir,tol];
AppendTo[out,points];
runQ=True;
mid=Round[(points[[1]]+points[[2]])/2];
AppendTo[midOut,mid];
While[Max[Abs[points[[1]]-points[[2]]]]>2&&runQ,
runPts=run[img,mid,dir,tol];
runQ=Max[Abs[mid-runPts]]>0;
If[runQ,
AppendTo[runOut,runPts];
points=reach[img,runPts,dir,tol];
AppendTo[out,points];
mid=Round[(points[[1]]+points[[2]])/2];
AppendTo[midOut,mid];
];
];
(* Flatten[out,1] *)
{If[MidQ,midOut],If[EdgeQ,out],If[RunQ,runOut]}/.Null->Sequence[]
]


(* ::Subsubsection:: *)
(*Fillament Fill : Init*)


pathLengths[path_]:=Module[{vecs},
vecs=Most[path]-Rest[path];
Map[(Sqrt[#[[1]]^2+#[[2]]^2])&,vecs]
]


Clear[pointsOnPath];
pointsOnPath[path:{_List,_List},n_]:=Module[{len,vec},
len=pathLengths[path];
vec=(path[[2]]-path[[1]])/n;
Table[path[[1]]+i vec,{i,0,n}]
]
pointsOnPath[path_,n_]:=Module[{lens,nums},
lens=pathLengths[path];
nums=Map[Ceiling[# n /Total[lens]]&,lens];
Flatten[Table[pointsOnPath[{path[[i]],path[[i+1]]},nums[[i]]],{i,1,Length[nums]}],1]
]

pointOnPath[path:{_List,_List},d_]:=Module[{len,vec},
len=pathLengths[path];
vec=(path[[2]]-path[[1]])/len[[1]];
path[[1]]+d vec
]
pointOnPath[path_,d_]:=Module[{lens,nums,dTemp,i},
lens=pathLengths[path];
i=0; dTemp=d;
While[dTemp-lens[[i+1]]>0 && i<Length[lens],i=i+1;dTemp=dTemp-lens[[i]];Print[i,": dTemp = ",dTemp]];
pointOnPath[{path[[i+1]],path[[i+2]]},dTemp]
]


fillamentFill[imgCls_,path_,dir_,filaments_]:=Module[{extraPts,extraReachPts,midFingerPts},
extraPts=Round[N[pointsOnPath[path,filaments]]];
extraReachPts=Table[reach[imgCls,extraPts[[i]],dir,{2,1}],{i,1,Length[extraPts]}];
midFingerPts=Map[Total,extraReachPts]/2;
{midFingerPts,extraReachPts}
]


(* ::Subsubsection:: *)
(*5.3. Exclude Points: Edge Points on Frame : init*)


edgePointsOnFramePos[img_,pts_,dir_]:=Module[{h,w,pattern},
{h,w}=Dimensions[img];
pattern = dir/. {{0,_}-> {1|h,_},{_,0}-> {_,1|w}};
Map[First,Position[pts,pattern]]
]


(* ::Subsubsection:: *)
(*5.4. Exclude Points: Estimated Tip Position : Init*)


tipEstimate[reachPts_,incPos_,dir_]:=Module[{pts,d,avg,tol,pos,indx},
indx=Position[dir,0][[1,1]];
pts=reachPts[[incPos]];
d = Map[Abs[(#[[1,indx]]-#[[2,indx]])]&,pts];
{avg, tol} = medianMean[d,0.5];
pos = Position[d,n_ /; n< avg-tol];
{Extract[incPos,pos],Delete[incPos,pos]}
]



(* ::Subsubsection:: *)
(*MidLine Fit : Init*)


Clear[kinkFit];
kinkFit[pts_,pos_:All,minPts:_:4,tol_:0.1]:=Module[{fitPts,lmStraight,lmF,lmB,res,resT,kinkPos,knucklePos},
If[TrueQ[pos==All],pos=Table[i,{i,1,Length[pts]}]];
fitPts=pts[[pos]];
lmStraight=LinearModelFit[fitPts,x,x];
res=Total[lmStraight["FitResiduals"]^2/Length[lmStraight["FitResiduals"]]];
If[res>tol,
lmF=Table[kinkedFit[pts,pos[[;;ii]],pos[[ii+1;;]]],{ii,minPts,Length[pos]-minPts-1}];
resT=Table[Total[lmF[[ii,2]]^2/Length[lmF[[ii,2]]]],{ii,1,Length[lmF]}];
kinkPos=Position[resT,Min[resT],1,1][[1,1]];
{lmF[[kinkPos,1]],If[TrueQ[pos==All],kinkPos+minPts-1,pos[[kinkPos+minPts-1]]]}
,
kinkPos=Round[Length[fitPts]/2];
knucklePos={fitPts[[kinkPos,1]],lmStraight[fitPts[[kinkPos,1]]]};
{{{pts[[1,1]],lmStraight[pts[[1,1]]]},{pts[[-1,1]], lmStraight[pts[[-1,1]]]}},If[TrueQ[pos==All],kinkPos,pos[[kinkPos]]]}
]
]
Clear[kinkedFit]
kinkedFit[pts_,posA_,posB_]:=Module[{lmStraight,lmA,cA,mA,lmB,cB,mB,cLim,linePntA,linePntB,linePntBB,linePntC,res,ptsB},
lmA=LinearModelFit[pts[[posA]],x,x];
cA=lmA[0]; mA=lmA[1]-cA;
linePntA={pts[[1,1]], lmA[pts[[1,1]]]};
linePntB={pts[[posA[[-1]],1]], lmA[pts[[posA[[-1]],1]]]};
cLim=lmA[pts[[posB[[1]],1]]]-lmA[pts[[posA[[-1]],1]]];
ptsB=Map[(#-linePntB)&,pts[[posB]] ];
lmB=LinearModelFit[ptsB,x,x,IncludeConstantBasis->True];
cB=lmB[0]; mB=lmB[1]-cB;
If[0<=cB<=cLim,
  linePntBB={pts[[posA[[-1]],1]]+cB/mA, lmA[pts[[posA[[-1]],1]]+cB/mA]},
  If[cB > cLim,
   (* cB > cLim *)
    linePntBB={pts[[posA[[-1]],1]]+cLim/mA, lmA[pts[[posA[[-1]],1]]+cLim/mA]};
    ptsB=Map[(#-linePntBB)&,pts[[posB]] ];
    lmB=LinearModelFit[ptsB,x,x,IncludeConstantBasis->False];
    cB=lmB[0]; mB=lmB[1]-cB;,
   (* cB < 0 *)
    linePntBB=linePntB;
    lmB=LinearModelFit[ptsB,x,x,IncludeConstantBasis->False];
    cB=lmB[0]; mB=lmB[1]-cB;
  ]
];
linePntC={pts[[-1,1]], lmB[pts[[-1,1]]-linePntBB[[1]]]+linePntBB[[2]]};
res=Flatten[{lmA["FitResiduals"],lmB["FitResiduals"]}];
{{linePntA,linePntBB,linePntC},res}
]


(* ::Subsubsection:: *)
(*Width Estimation and non parallel edge points exclusion. : Init*)


distanceParallelLines[lineA_Function,lineB_Function]:=Module[{m,cA,cB},
cA=lineA[0];cB=lineB[0];m=lineA[1]-cA;
Abs[cB-cA]/Sqrt[m^2+1]
]
distanceParallelLines[lineA:{{_,_},{_,_}},lineB:{{_,_},{_,_}}]:=Module[{m,cA,cB,aA,aB,bA,bB,lineAF,lineBF},
lineAF=pointsToEquation[lineA[[1]],lineA[[2]]];
lineBF=pointsToEquation[lineB[[1]],lineB[[2]]];
cA=lineAF[0,0]; aA=lineAF[1,0]-cA; bA=lineAF[0,1]-cA;
cB=lineBF[0,0]; aB=lineBF[1,0]-cB; bB=lineBF[0,1]-cB;  
Abs[cB-cA]/Sqrt[aA^2+aB^2]
]


parallelFit[pnts_,line_Function]:=Module[{pPnts,fun,res,tipPos},
pPnts=Map[(#-{0,line[#[[1]]]})&,pnts];
fun=Function[{x},Evaluate[Normal[line[x]]+Fit[pPnts,{1},x]]];
res=Map[(fun[#[[1]]]-#[[2]])&,pnts];
(* Remove points which are far from the line *);
tipPos=Position[Thread[Abs[res]>Total[Abs[res]]/Length[res]],True];
pPnts=Delete[pPnts,tipPos];
fun=Function[{x},Evaluate[Normal[line[x]]+Fit[pPnts,{1},x]]];
{fun,tipPos}
]
parallelFit[pnts_,linePnts:{{_,_},{_,_}}]:=Module[{pPnts,fun,res,tipPos,line},
line=pointsToEquationX[linePnts[[1]],linePnts[[2]]];
pPnts=Map[(#-{0,line[#[[1]]]})&,pnts];
fun=Function[{x},Evaluate[Normal[line[x]]+Fit[pPnts,{1},x]]];
res=Map[(fun[#[[1]]]-#[[2]])&,pnts];
(* Remove points which are far from the line *);
tipPos=Position[Thread[Abs[res]>Total[Abs[res]]/Length[res]],True];
pPnts=Delete[pPnts,tipPos];
fun=Function[{x},Evaluate[Normal[line[x]]+Fit[pPnts,{1},x]]];
{fun,tipPos}
]


Clear[perpDistToline]

perpDistToline[fun_Function, pnt:{_,_}] := Module[{f, g, a, b, m, c, d}, 
a=pnt[[1]]; b=pnt[[2]];
c = fun[0]; 
m = fun[1] - c; 
f[x_, mm_, cc_] := mm*x + cc; 
g[x_, mm_, aa_, bb_] := bb - (1/mm)*(x - aa); 
   {(m a + c - b)/Sqrt[1 + m^2], Line[{{a, b}, {(a + b m - c m)/(1 + m^2), g[(a + b m - c m)/(1 + m^2), m, a, b]}}]}
 ]
perpDistToline[line:{{_,_},{_,_}}, pnt:{_,_}] := Module[{f, g, a, b, c, lineF, perpVec, dist, pntOnLine}, 
lineF=pointsToEquation[line[[1]],line[[2]]];
c=lineF[0,0]; a=lineF[1,0]-c; b=lineF[0,1]-c;
perpVec={a,b}/Sqrt[a^2+b^2]; 
dist=((line[[2,2]]-line[[1,2]]) pnt[[1]] - (line[[2,1]]-line[[1,1]] )pnt[[2]]+line[[2,1]] line[[1,2]] - line[[2,2]] line[[1,1]] )/Sqrt[(line[[2,2]]-line[[1,2]])^2 + (line[[2,1]]-line[[1,1]])^2];
pntOnLine=pnt +dist perpVec;
   {{Abs[dist],Sqrt[(pntOnLine[[1]]-line[[1,1]])^2 +(pntOnLine[[2]]-line[[1,2]])^2] }, Line[{pnt, pntOnLine}]}
 ]
perpDistToline[fun_, pnt:{Except[_List],Except[_List]},limits:{{_,_},{_,_}},limitQ:{_,_}:{True,True}] := Module[{xLims,yLims,dist,line}, 
xLims=Sort[{limits[[1,1]],limits[[2,1]]}];
yLims=Sort[{limits[[1,2]],limits[[2,2]]}];
{dist,line} = perpDistToline[fun, pnt];
If[If[limitQ[[1]],(xLims[[1]]<=line[[1,2,1]]<=xLims[[2]]),True]&&If[limitQ[[2]],(yLims[[1]]<=line[[1,2,2]]<=yLims[[2]]),True],
{dist,line},
{{0,0},Point[pnt]}
 ]
]
perpDistToline[fun_, pnt_List] := Module[{dLine}, 
dLine=Map[perpDistToline[fun, #]&,pnt];
{dLine[[All,1]],dLine[[All,2]]}
 ]
perpDistToline[fun_, pnt_List, limits:{{_,_},{_,_}},limitQ:{_,_}:{True,True}] := Module[{dLine, pos}, 
dLine=Map[perpDistToline[fun, #,limits, limitQ]&,pnt];
pos=Position[dLine, {{Except[0],_},_},{1}];
dLine = dLine /. {{{0,_},_}->Sequence[]};
{dLine[[All,1]],dLine[[All,2]],pos}
 ]


pointsToEquation[pntA_,pntB_]:=Module[{},
Function[{x,y},Evaluate[
(pntB[[1]]-pntA[[1]])(y-pntA[[2]])-(pntB[[2]]-pntA[[2]])(x-pntA[[1]])]]
]
pointsToEquationX[pntA_,pntB_]:=Module[{m,c,x},
m = (pntB[[2]]-pntA[[2]])/(pntB[[1]]-pntA[[1]]);
c = pntA[[2]]- m pntA[[1]];
Function[{x},Evaluate[m x + c]]
]
pointsToEquationY[pntA_,pntB_]:=Module[{m,c,x},
pointsToEquationX[Reverse[pntA],Reverse[pntB]]
]


Clear[FixAspectRatio]
FixAspectRatio[in_,limits_,target_]:=Module[{inRng,targetRng,targetAspt,inAspt,drng,first,cond,out},
inRng={in[[1,2]]-in[[1,1]],in[[2,2]]-in[[2,1]]};
inAspt=inRng[[2]]/inRng[[1]];
targetAspt=(target[[2,2]]-target[[2,1]])/(target[[1,2]]-target[[1,1]]);
If[inAspt > targetAspt,
drng = {inRng[[2]]/targetAspt -inRng[[1]],0},
drng = {0,inRng[[1]] targetAspt-inRng[[2]]}
];
first= {{in[[1,1]]-drng[[1]]/2,in[[1,2]]+drng[[1]]/2},{in[[2,1]]-drng[[2]]/2,in[[2,2]]+drng[[2]]/2}};
out=first;
cond=limits-first;
If[cond[[1,1]]>0, out[[1,1]]= out[[1,1]]+cond[[1,1]];out[[1,2]]= out[[1,2]]+cond[[1,1]]];
If[cond[[1,2]]<0, out[[1,1]]= out[[1,1]]+cond[[1,2]];out[[1,2]]= out[[1,2]]+cond[[1,2]]];
If[cond[[2,1]]>0, out[[2,1]]= out[[2,1]]+cond[[2,1]];out[[2,2]]= out[[2,2]]+cond[[2,1]]];
If[cond[[2,2]]<0, out[[2,1]]= out[[2,1]]+cond[[2,2]];out[[2,2]]= out[[2,2]]+cond[[2,2]]];
out
]


PointSetDataRange[pnts_]:=Module[{pntRng,pntsX,pntsY},
pntRng=Map[(1;;#)&,Most[Dimensions[pnts]]];
pntsX=pnts[[All,All,1]];
pntsY = pnts[[All,All,2]];
{{Min[pntsX],Max[pntsX]},{Min[pntsY],Max[pntsY]}}
]


FindWidths[extraReachPts_,midLineFit_,toStd_,fromStd_]:=Module[{middleQ,midLineFitStd,extraReachPtsStd1,extraReachPtsStd2,minPts=3,
dDistal1,dDistal1Lines,dDistal1Pos,dDistal2,dDistal2Lines,dDistal2Pos,distalLength,
dMiddle1,dMiddle1Lines,dMiddle1Pos,dMiddle2,dMiddle2Lines,dMiddle2Pos,
widthD1,tolD1,widthD2,tolD2,widthD,tolD,dDistal1GoodPos,dDistal2GoodPos,widthM1,tolM1,widthM2,tolM2,widthM,tolM,dMiddle1GoodPos,dMiddle2GoodPos,
pntClassPos,sausageDistalFit,sausageMiddleFit,middleWidth,distalWidth,width,lines},
midLineFitStd=toStd[midLineFit];
extraReachPtsStd1=toStd[extraReachPts[[All,1]]];
extraReachPtsStd2=toStd[extraReachPts[[All,2]]];
middleQ=Length[midLineFit]>=3;
If[middleQ,
{dDistal1,dDistal1Lines,dDistal1Pos}=perpDistToline[midLineFitStd[[2;;3]], extraReachPtsStd1,midLineFitStd[[2;;3]],{True,True}];
{dDistal2,dDistal2Lines,dDistal2Pos}=perpDistToline[midLineFitStd[[2;;3]], extraReachPtsStd2,midLineFitStd[[2;;3]],{True,True}];
  distalLength=Sqrt[(midLineFitStd[[2,1]]-midLineFitStd[[3,1]])^2 + (midLineFitStd[[2,2]]-midLineFitStd[[3,2]])^2];
{dMiddle1,dMiddle1Lines,dMiddle1Pos}=perpDistToline[midLineFitStd[[1;;2]], extraReachPtsStd1,midLineFitStd[[1;;2]],{True,True}];
{dMiddle2,dMiddle2Lines,dMiddle2Pos}=perpDistToline[midLineFitStd[[1;;2]], extraReachPtsStd2,midLineFitStd[[1;;2]],{True,True}];
dMiddle1[[All,2]]=dMiddle1[[All,2]]+distalLength;
dMiddle2[[All,2]]=dMiddle2[[All,2]]+distalLength,
{dDistal1,dDistal1Lines,dDistal1Pos}=perpDistToline[midLineFitStd[[1;;2]], extraReachPtsStd1,midLineFitStd[[1;;2]],{True,True}];
{dDistal2,dDistal2Lines,dDistal2Pos}=perpDistToline[midLineFitStd[[1;;2]], extraReachPtsStd2,midLineFitStd[[1;;2]],{True,True}];
];
 middleQ = middleQ && Length[dMiddle1]>= minPts && Length[dMiddle2]>= minPts;
{widthD1,tolD1}=medianMean[dDistal1[[All,1]],0.5];
{widthD2,tolD2}=medianMean[dDistal2[[All,1]],0.5];
{widthD,tolD}= {(widthD1+widthD2)/2,Max[{tolD1,tolD2}]};
dDistal1GoodPos=Extract[dDistal1Pos ,Position[dDistal1[[All,1]],n_ /; n > (widthD- tolD) && n < (widthD+ tolD)  ]];
dDistal2GoodPos=Extract[dDistal2Pos ,Position[dDistal2[[All,1]],n_ /; n > (widthD- tolD) && n < (widthD+ tolD)  ]];
If[middleQ,
{widthM1,tolM1}=medianMean[dMiddle1[[All,1]],0.75];
{widthM2,tolM2}=medianMean[dMiddle2[[All,1]],0.75];
{widthM,tolM}= {(widthM1+widthM2)/2,Max[{tolM1,tolM2}]};
dMiddle1GoodPos=Extract[dMiddle1Pos ,Position[dMiddle1[[All,1]],n_ /; n > (widthM- tolM) && n < (widthM+ tolM)  ]];
dMiddle2GoodPos=Extract[dMiddle2Pos ,Position[dMiddle2[[All,1]],n_ /; n > (widthM- tolM) && n < (widthM+ tolM)  ]];
 middleQ = middleQ && Length[dMiddle1GoodPos]>= minPts && Length[dMiddle2GoodPos]>= minPts;,
dMiddle1GoodPos={}; dMiddle2GoodPos={};
];
(* (Top, Bottom) (Middle, Distal, Tip)*)
If[middleQ,
pntClassPos={
{{Flatten[dMiddle1GoodPos], Flatten[Complement[dMiddle1Pos,dMiddle1GoodPos]]},
{Flatten[dDistal1GoodPos],Flatten[Complement[dDistal1Pos,dDistal1GoodPos]]},Table[i,{i,dDistal1GoodPos[[-1,1]],Length[extraReachPtsStd1]}]},
{{Flatten[dMiddle2GoodPos], Flatten[Complement[dMiddle2Pos,dMiddle2GoodPos]]},
{Flatten[dDistal2GoodPos],Flatten[Complement[dDistal2Pos,dDistal2GoodPos]]},Table[i,{i,dDistal2GoodPos[[-1,1]],Length[extraReachPtsStd2]}]}};,
pntClassPos={
{{},
{Flatten[dDistal1GoodPos],Flatten[Complement[dDistal1Pos,dDistal1GoodPos]]},Table[i,{i,dDistal1GoodPos[[-1,1]],Length[extraReachPtsStd1]}]},
{{},
{Flatten[dDistal2GoodPos],Flatten[Complement[dDistal2Pos,dDistal2GoodPos]]},Table[i,{i,dDistal2GoodPos[[-1,1]],Length[extraReachPtsStd2]}]}}
];

If[middleQ,
lines={ {dMiddle1Lines, dDistal1Lines}, {dMiddle2Lines, dDistal2Lines}};,
lines={ {{},dDistal1Lines}, {{},dDistal2Lines}}
];

If[middleQ,
sausageDistalFit={
 parallelFit[Extract[extraReachPtsStd1,dDistal1GoodPos],midLineFitStd[[2;;3]]],
parallelFit[Extract[extraReachPtsStd2,dDistal2GoodPos],midLineFitStd[[2;;3]]]};
distalWidth=distanceParallelLines[sausageDistalFit[[1,1]],sausageDistalFit[[2,1]]];
sausageMiddleFit={
 parallelFit[Extract[extraReachPtsStd1,dMiddle1GoodPos],midLineFitStd[[1;;2]]],
parallelFit[Extract[extraReachPtsStd2,dMiddle2GoodPos],midLineFitStd[[1;;2]]]};
middleWidth=distanceParallelLines[sausageMiddleFit[[1,1]],sausageMiddleFit[[2,1]]];,
sausageDistalFit={
 parallelFit[Extract[extraReachPtsStd1,dDistal1GoodPos],midLineFitStd[[{-2,-1}]]],
parallelFit[Extract[extraReachPtsStd2,dDistal2GoodPos],midLineFitStd[[{-2,-1}]]]};
distalWidth=distanceParallelLines[sausageDistalFit[[1,1]],sausageDistalFit[[2,1]]];
 middleWidth=0;
];

If[middleQ,
width={middleWidth,distalWidth},
width={0,distalWidth}
];
{width,pntClassPos,middleQ,lines}
]


(* ::Subsubsection:: *)
(*Model The Tip. : Init.*)


Clear[AngleInequality];
AngleInequality[\[Phi]1_,\[Phi]2_]:=Module[{toP,toPM},
toP=Function[{\[Phi]},Mod[\[Phi],2Pi]];
Function[{\[Theta]},0<= Mod[\[Theta]-"\[Phi]1",2Pi]<= toP["\[Phi]2"-"\[Phi]1"]]/.{"\[Phi]1"->toP[\[Phi]1],"\[Phi]2"->toP[\[Phi]2]}
]


Clear[ellipseBoundingBox]
ellipseBoundingBox[{tri_,{center_,{a_,b_},\[Phi]_}},{pos_,\[Theta]_}]:=Module[{i,\[Theta]lim,\[Psi],t1,t2,t,angles,dn,pnts},
\[Theta]lim=AngleInequality[ArcTan[tri[[2,2,2]]/tri[[2,2,1]]]-\[Theta],ArcTan[tri[[1,2,2]]/tri[[1,2,1]]]-\[Theta]];
\[Psi]=-(\[Phi]+\[Theta]);
t1=ArcTan[-b Tan[\[Psi]]/a];
t2=ArcTan[ b Cot[\[Psi]]/a];
angles={{t1,t1+Pi},{t2,t2+Pi}};
dn=Flatten[{
Map[Function[{t},{a Cos[t] Cos[\[Psi]]-b Sin[t] Sin[\[Psi]], b*Sin[t]*Cos[\[Psi]]+a*Cos[t]*Sin[\[Psi]]}+center],angles[[1]]],
Map[Function[{t},{a Cos[t] Cos[\[Psi]]-b Sin[t] Sin[\[Psi]], b*Sin[t]*Cos[\[Psi]]+a*Cos[t]*Sin[\[Psi]]}+center],angles[[2]]]
},1];
pnts=Map[(#+pos)&,dn];
{{Min[pnts[[All,1]]],Max[pnts[[All,1]]]},{Min[pnts[[All,2]]],Max[pnts[[All,2]]]}}
]


Clear[modelToGraphics]
IncludePoints::usage="Option for modelToGraphics: Include points at corners and center of the ellipse.";
Colors::usage="Option for modelToGraphics: {distalColor,tipColors}";
Options[modelToGraphics]={IncludePoints->True,Colors->{Opacity[0.4,Yellow],Opacity[0.4,Magenta]}};

modelToGraphics[model_,{pos_,\[Theta]_},OptionsPattern[]]:=Module[{trap,elpse,\[Phi]2,\[Phi]1,tmp,tmb,includePoints,colors},
colors=OptionValue[Colors];
includePoints=OptionValue[IncludePoints];
trap=model[[1]];
elpse=model[[2]];
\[Phi]2=ArcTan[Sequence@@(trap[[1,2]]-elpse[[1]])];
\[Phi]1=ArcTan[Sequence@@(trap[[2,2]]-elpse[[1]])];
Translate[Rotate[{
{EdgeForm[Directive[colors[[1]]]],FaceForm[colors[[1]]],
Polygon[Flatten[{trap[[1]],Reverse[trap[[2]]]},1]],
EdgeForm[Directive[colors[[2]]]],FaceForm[colors[[2]]],
ellipse[elpse,{\[Phi]1,\[Phi]2}]},
If[includePoints,
  {Black,PointSize[Medium], Point[elpse[[1]]], Point[Flatten[trap,1]]},Sequence[]]
},-\[Theta],elpse[[1]]],pos]
]

modelToGraphics[model_,{pos_,\[Theta]_},colors_,opts:OptionsPattern[]]:=Module[{trap,elpse,\[Phi]2,\[Phi]1,tmp,tmb,includePoints},
modelToGraphics[model,{pos,\[Theta]},{Colors->colors,IncludePoints->OptionValue[modelToGraphics,opts,IncludePoints]}]
]


Clear[modelToPolygon]
modelToPolygon[model_,{pos_,\[Theta]_}]:=Module[{trap,elpse,\[Phi]2,\[Phi]1,tmp,tmb,pts,ePts,mdl},
mdl=translateModel[model,-model[[2,1]]];
trap=mdl[[1]];
elpse=mdl[[2]];
\[Phi]2=ArcTan[Sequence@@(trap[[1,2]]-elpse[[1]])];
\[Phi]1=ArcTan[Sequence@@(trap[[2,2]]-elpse[[1]])];
ePts=(ellipse[elpse,{\[Phi]1,\[Phi]2},"Open"])[[1,1]];
pts=Map[(#+pos+model[[2,1]])&,Transpose[RotationMatrix[-\[Theta]].Transpose[Flatten[{trap[[2]],ePts,Reverse[trap[[1]]]},1]]]];
Polygon[pts]
]


Clear[paramEllipseFunction]; 
paramEllipseFunction[{{x0_, y0_}, {a_, b_}, \[Phi]_}] := Module[{t}, 
Function[{t}, Evaluate[{x0 + (a*b*Cos[t])/Sqrt[b^2*Cos[t - \[Phi]]^2 + a^2*Sin[t - \[Phi]]^2], y0 + (a*b*Sin[t])/Sqrt[b^2*Cos[t - \[Phi]]^2 + a^2*Sin[t - \[Phi]]^2]}]]
]


fixEllipseThroughPoints[pts_,elpse_]:=Module[{\[Phi]1,\[Phi]2,ellipseFun,newPts},
\[Phi]1=ArcTan[pts[[1,1]]-elpse[[1,1]],pts[[1,2]]-elpse[[1,2]]]; 
\[Phi]2=ArcTan[pts[[2,1]]-elpse[[1,1]],pts[[2,2]]-elpse[[1,2]]];
ellipseFun=paramEllipseFunction[{elpse[[1]],elpse[[2]],elpse[[3]]}];
newPts={pts[[2]],Sequence@@Table[ellipseFun[\[Phi]2+p(\[Phi]1-\[Phi]2)],{p,0.25,0.75,0.25}],pts[[1]]};
EllipseFit[newPts,"Direct"]
]


Options[findModel]={EdgeAlignment->True,EllipseAlignment->True,MassCentered->True};
EdgeAlignment::usage="Option for findModel, Are the ellipse and trapezium edges to be aligned?"
EllipseAlignment::usage="Option for findModel, Is the digit axis or the ellipse axis to be used?"
MassCentered::usage="Option for findModel, Center on the center of mass for the model?"
findModel[pts_,midPts_,midLine_,pntPos_,std\[Theta]_,std_,w_,OptionsPattern[]]:=Module[{midLineStd,ptsStd1,ptsStd2,midPtsStd,
 dp1,dp2,d2,d1,tiltAdjust,midPtsStdDistal,lm,\[Theta],origin,toNeut1,toNeut2,ptsNeut1,ptsNeut2,
 posSide, posTip, edgeFit, edgeFitMM, distEdgeFun, distEdge, posSideTip, ptsSTNewt, sides, tipEllipse, tipEllipseDirect, tipEllipseAMS,
 model,modelPos,modelA,modelPosA,modelB,modelPosB,modelC,modelPosC,modelD,modelPosD,dPos1,dPos2,trapC,cm,
 posSideTipA, ptsSTNewtA, sidesA},
(* 
findModel[extraReachPts[[i,j]],midFingerPts[[i,j]],midLineFit[[i,j]],pntClassPos[[i,j]],direction\[Theta][[i,j]],toStd[[i,j]],width[[i,j]]]
pts = extraReachPts[[i,j]];
midPts = midFingerPts[[i,j]];
midLine = midLineFit[[i,j]];
pntPos = pntClassPos[[i,j]];
std\[Theta] = direction\[Theta][[i,j]];
std = toStd[[i,j]];
w = width[[i,j]];
 *)

(* Put Points into Standard position*)
midLineStd    = std[midLine];
ptsStd1       = std[pts[[All,1]]];
ptsStd2       = std[pts[[All,2]]];
midPtsStd     = std[midPts];
(* Biologically determined points on midline *)
tiltAdjust=Abs[(midLineStd[[-2]][[2]]-midLineStd[[-1]][[2]])/(2(midLineStd[[-2]][[1]]-midLineStd[[-1]][[1]]))];
If[tiltAdjust>0.25,tiltAdjust=0.25];
dp2 = distanceOnLine[Reverse[midLineStd],w[[2]](1.5 ) ];
dp1 = distanceOnLine[Reverse[midLineStd],w[[2]](0.5 ) ];
d2  = distanceOnLine[Reverse[midLineStd],w[[2]](1.5 -tiltAdjust) ];
d1  = distanceOnLine[Reverse[midLineStd],w[[2]](0.5 +tiltAdjust) ];
midPtsStdDistal=midPtsStd[[Flatten[Position[midPtsStd [[All,1]],n_ /; d1[[1]]>n>d2[[1]] ]] ]];

(* Fit Midpoints between limits *)
lm=LinearModelFit[midPtsStdDistal,x,x,Weights->With[{l=Length[midPtsStdDistal]-1},Table[E^(-((x-l/2)^2/ (l^2))),{x,0,l,1}]]];
\[Theta]=-ArcTan[lm["BestFitParameters"][[2]]];
origin = {dp2[[1]],lm[dp2[[1]]]};
(* Newtral Orientation Pts *)
toNeut1=Function[{ppts},Transpose[        RotationMatrix[\[Theta]] . Transpose[Map[(#-origin)&,ppts]]]];
toNeut2=Function[{ppts},Transpose[({1,-1} RotationMatrix[\[Theta]]). Transpose[Map[(#-origin)&,ppts]]]];
ptsNeut1=toNeut1[ptsStd1];
ptsNeut2=toNeut2[ptsStd2];
(* Position of corresponding edge points *)
posSide={
Flatten[Position[ptsNeut1[[All,1]], n_ /; 0<n<w[[2]] ]], Flatten[Position[ptsNeut2[[All,1]], n_ /; 0<n<w[[2]] ]]
};
posTip={
Flatten[Position[ptsNeut1[[All,1]], n_ /; w[[2]] <=  n ]], Flatten[Position[ptsNeut2[[All,1]], n_ /; w[[2]] <=  n ]]
};
(* Fit Edge points between limits *)
edgeFit=LinearModelFit[{Sequence@@ptsNeut1[[posSide[[1]]]],Sequence@@ptsNeut2[[posSide[[2]]]]},x,x];
edgeFitMM=medianMean[Abs[edgeFit["FitResiduals"]],0.9];
(* Tip position fun *)
distEdgeFun=Function[{pnt},Map[perpDistToline[{{ptsNeut1[[1,1]],edgeFit[ptsNeut1[[1,1]]]},{ptsNeut1[[-1,1]],edgeFit[ptsNeut1[[-1,1]]]}}, #]&,pnt]];
distEdge={distEdgeFun[ptsNeut1],distEdgeFun[ptsNeut2]};
(* unMoved Tip position *)
posSideTipA={{Range[posSide[[1,1]],posSide[[1,-1]]],Range[posSide[[1,-1]],Length[distEdge[[1]]]]},
             {Range[posSide[[2,1]],posSide[[2,-1]]],Range[posSide[[2,-1]],Length[distEdge[[2]]]]}};

ptsSTNewtA={{toNeut1[ptsStd1[[posSideTipA[[1,1]]]]],toNeut1[ptsStd1[[posSideTipA[[1,2]]]]] },
            {toNeut1[ptsStd2[[posSideTipA[[2,1]]]]],toNeut1[ptsStd2[[posSideTipA[[2,2]]]]] }};
sidesA=Block[{x11=ptsSTNewtA[[1,1,1,1]],x12=ptsSTNewtA[[1,1,-1,1]],x21=ptsSTNewtA[[2,1,1,1]],x22=ptsSTNewtA[[2,1,-1,1]]},
{{{x11,edgeFit[x11]},{x12,edgeFit[x12]}},{{x21,-edgeFit[x21]},{x22,-edgeFit[x22]}}} ];
(* Move Tip position if needed *)
dPos1=0; dPos2=0;
While[posSide[[1,-1]]+dPos1 < Length[distEdge[[1]]] && distEdge[[1,posSide[[1,-1]]+dPos1+1]] < 2 edgeFitMM[[2]], dPos1=dPos1+1];
While[posSide[[2,-1]]+dPos2 < Length[distEdge[[2]]] && distEdge[[2,posSide[[2,-1]]+dPos2+1]] < 2 edgeFitMM[[2]], dPos2=dPos2+1];
If[dPos1==0,
While[posSide[[1,-1]]+dPos1>posSide[[1,1]]          && distEdge[[1,posSide[[1,-1]]+dPos1-1]] > 2 edgeFitMM[[2]], dPos1=dPos1-1]
];
If[dPos2==0,
While[posSide[[2,-1]]+dPos2>posSide[[1,1]]          && distEdge[[2,posSide[[2,-1]]+dPos2-1]] > 2 edgeFitMM[[2]], dPos2=dPos2-1]
];
posSideTip={{Range[posSide[[1,1]],posSide[[1,-1]]+dPos1],Range[posSide[[1,-1]]+dPos1,Length[distEdge[[1]]]]},
            {Range[posSide[[2,1]],posSide[[2,-1]]+dPos2],Range[posSide[[2,-1]]+dPos2,Length[distEdge[[2]]]]}};

ptsSTNewt={{toNeut1[ptsStd1[[posSideTip[[1,1]]]]],toNeut1[ptsStd1[[posSideTip[[1,2]]]]] },
           {toNeut1[ptsStd2[[posSideTip[[2,1]]]]],toNeut1[ptsStd2[[posSideTip[[2,2]]]]] }};
sides=Block[{x11=ptsSTNewt[[1,1,1,1]],x12=ptsSTNewt[[1,1,-1,1]],x21=ptsSTNewt[[2,1,1,1]],x22=ptsSTNewt[[2,1,-1,1]]},
{{{x11,edgeFit[x11]},{x12,edgeFit[x12]}},{{x21,-edgeFit[x21]},{x22,-edgeFit[x22]}}} ];
tipEllipseDirect=EllipseFit[{Sequence@@ptsSTNewt[[1,1,-3;;]],Sequence@@ptsSTNewt[[1,2]],Sequence@@ptsSTNewt[[2,2]],Sequence@@ptsSTNewt[[2,1,-3;;]]},"Direct"];
tipEllipseAMS=EllipseFit[{Sequence@@ptsSTNewt[[1,1,-3;;]],Sequence@@ptsSTNewt[[1,2]],Sequence@@ptsSTNewt[[2,2]],Sequence@@ptsSTNewt[[2,1,-3;;]]},"AMS"];
(* The first Model *)
modelA={{{sides[[1,1]]-tipEllipseDirect[[1]],sides[[1,2]]-tipEllipseDirect[[1]]},{sides[[2,1]]-tipEllipseDirect[[1]],sides[[2,2]]-tipEllipseDirect[[1]]}},{{0,0},tipEllipseDirect[[2]],tipEllipseDirect[[3]]}};
modelPosA={RotationMatrix[-std\[Theta] ].(RotationMatrix[-\[Theta]].tipEllipseDirect[[1]]+origin), std\[Theta]+\[Theta]};
(* Fix the ellipse to the trapesium *)
tipEllipse=fixEllipseThroughPoints[{sides[[1,2]],sides[[2,2]]},tipEllipseDirect] ;
modelB={{{sides[[1,1]]-tipEllipse[[1]],sides[[1,2]]-tipEllipse[[1]]},{sides[[2,1]]-tipEllipse[[1]],sides[[2,2]]-tipEllipse[[1]]}},{{0,0},tipEllipse[[2]],tipEllipse[[3]]}};
modelPosB={RotationMatrix[-std\[Theta] ].(RotationMatrix[-\[Theta]].tipEllipse[[1]]+origin), std\[Theta]+\[Theta]};
(* Rotate into neutral Orientation for the ellipse *)
trapC=Transpose[RotationMatrix[-modelB[[2]][[3]] ].Transpose[Flatten[modelB[[1]],1]]];
modelC={{trapC[[1;;2]],trapC[[3;;4]]},{modelB[[2,1]],modelB[[2,2]],0}};
modelPosC={RotationMatrix[-std\[Theta] ].(RotationMatrix[-\[Theta]].tipEllipse[[1]]+origin), std\[Theta]+\[Theta]-modelB[[2]][[3]]};
If[OptionValue[EdgeAlignment],
If[OptionValue[EllipseAlignment],
If[OptionValue[MassCentered],
  cm=RegionCentroid[(modelToPolygon[modelC,{{0,0},0}] )];
  {translateModel[modelC,cm],{modelPosC[[1]]-cm, modelPosC[[2]]}},
  {modelC,modelPosC}
],
If[OptionValue[MassCentered],
  cm=RegionCentroid[(modelToPolygon[modelB,{{0,0},0}] )];
  {translateModel[modelB,cm],{modelPosB[[1]]-cm, modelPosB[[2]]}},
  {modelB,modelPosB}
]
],
If[OptionValue[MassCentered],
  cm=RegionCentroid[(modelToPolygon[modelA,{{0,0},0}] )];
  {translateModel[modelA,cm],{modelPosA[[1]]-cm, modelPosA[[2]]}},
  {modelA,modelPosA}
]
]
]



plotRange[plot:(_Graphics|_Graphics3D|_Graph)]:=Reap[NotebookDelete[First@{PrintTemporary[Show[plot,Axes->True,Frame->False,Ticks->((Sow[{##}];Automatic)&),DisplayFunction->Identity,PlotRangePadding->None,ImageSize->0]],FinishDynamic[]}]][[2,1]]

completePlotRange[plot:(_Graphics|_Graphics3D|_Graph)]:=Reap[NotebookDelete[First@{PrintTemporary[Show[plot,Axes->True,Frame->False,Ticks->((Sow[{##}];Automatic)&),DisplayFunction->Identity,ImageSize->0]],FinishDynamic[]}]][[2,1]]


ClearAll[pntSymbol,pntSymbolStick,txtRadius];
txtRadius[txt_,imgSize:_Integer]:=Module[{},
txtRadius[txt,{imgSize,imgSize}]
];
txtRadius[txt_,imgSize:{_,_}:{350,350}]:=Module[{d},
d=Rasterize[txt,"RasterSize"];
Sqrt[( d[[1]]/( 2 imgSize[[1]]))^2+( d[[2]]/( 2 imgSize[[2]]))^2]
];
pntSymbol[xy_,sym_,color_:Green,imgSize_:{350,350}]:=Module[{txt,d,dp},
txt = Text[Style[sym,14]];
dp =  txtRadius[txt,imgSize] + 5 If[Length[imgSize]>1,1/Sqrt[imgSize[[1]]^2+imgSize[[2]]^2],1/imgSize];
{EdgeForm[Black],FaceForm[color],Disk[xy,Scaled[{dp,dp}]],Black,Text[txt,xy,{0,0}]}
];
pntSymbolStick[{x_,y_},sym_,color_:Green,\[Theta]_:0,imgSize_:{350,350}]:=Module[{dp=0.02,txtR,xyp},
txtR = txtRadius[Text[Style[sym,14]],imgSize] + If[Length[imgSize]>1,1/Sqrt[imgSize[[1]]^2+imgSize[[2]]^2],1/imgSize];
xyp=ImageScaled[{2 (txtR+dp) Cos[\[Theta]], 2 (txtR+dp) Sin[\[Theta]]},{x,y}];
{Line[{xyp,{x,y}}],pntSymbol[xyp,sym,color,imgSize],EdgeForm[Black],FaceForm[color],Disk[{x,y},Scaled[{dp/2, dp/2}]]}
];


Clear[angleSymbol]
angleSymbol[xy_,sym_,\[Phi]1\[Phi]2_List,color_:Green,imgSize_:{350,350}]:=Module[{txt,d,dp,\[Phi],\[Phi]0,txtR,txtPnt,\[Phi]1,\[Phi]2},
{\[Phi]1,\[Phi]2}=Sort[\[Phi]1\[Phi]2];
\[Phi]=\[Phi]2-\[Phi]1;
\[Phi]0=(\[Phi]2+\[Phi]1)/2;
txt = Text[Style[sym,14]];
dp =  txtRadius[txt,imgSize] + 5 If[Length[imgSize]>1,1/Sqrt[imgSize[[1]]^2+imgSize[[2]]^2],1/imgSize];
txtR=If[\[Phi]<Pi,dp/Sin[\[Phi]/2],1.1 Max[dp]/2];
txtPnt=ImageScaled[{txtR Cos[\[Phi]0],txtR Sin[\[Phi]0]},xy];
{EdgeForm[Black],FaceForm[color],Disk[xy,ImageScaled[{txtR+dp,txtR+dp}],{\[Phi]1,\[Phi]2}],Black,Text[txt,txtPnt,{0,0}]}
];


Clear[angleSymbolR]
angleSymbolR[xy_,sym_,{\[Phi]1_,\[Phi]2_},color_:Green,imgSize_:{350,350}]:=Module[{txt,d,dp,\[Phi],\[Phi]0,txtR,txtPnt},
\[Phi]=\[Phi]2-\[Phi]1;
\[Phi]0=(\[Phi]2+\[Phi]1)/2;
txt = Text[Style[sym,14]];
d=Rasterize[txt,"RasterSize"];
dp={d[[1]]/imgSize[[1]],d[[2]]/imgSize[[2]]};
txtR=If[\[Phi]<Pi,dp[[2]]/(2 Sin[\[Phi]/2])+dp[[1]]/2,1.1 Max[dp]/2];
txtPnt=ImageScaled[{txtR Cos[\[Phi]0],txtR Sin[\[Phi]0]},xy];
{color,Line[{xy,xy+{Cos[\[Phi]1],Sin[\[Phi]1]}}],
Line[{xy,xy+{Cos[\[Phi]2],Sin[\[Phi]2]}}],
,EdgeForm[Black],FaceForm[color],Disk[xy,ImageScaled[{txtR+1.2 dp[[1]]/2,txtR+1.2 dp[[1]]/2}],{\[Phi]1,\[Phi]2}],
Black,Text[txt,txtPnt,{0,0},{Cos[If[Mod[\[Phi]0-Pi/2,2Pi]<Pi,\[Phi]0+Pi,\[Phi]0]],Sin[If[Mod[\[Phi]0-Pi/2,2Pi]<Pi,\[Phi]0+Pi,\[Phi]0]]}]}
];


Clear[AngleScaled]
Options[AngleScaled]={PlotRange->{{0,1},{0,1}},ImageSize->{350,350}};
Attributes[AngleScaled]={Listable};
AngleScaled[\[Theta]_,OptionsPattern[]]:=Module[{scale,pos,imgSize,pltRng,n\[Theta],d\[Theta],np\[Theta],dp\[Theta],n},
n=Floor[\[Theta]/(Pi/2)];
n\[Theta]=n Pi/2;
d\[Theta]=Mod[\[Theta],Pi/2];
pltRng=OptionValue[PlotRange];
imgSize = OptionValue[ImageSize];
scale={imgSize[[1]]/(pltRng[[1,2]]-pltRng[[1,1]]),
imgSize[[2]]/(pltRng[[2,2]]-pltRng[[2,1]])};
pos=If[EvenQ[n],{scale[[1]]Cos[d\[Theta]],scale[[2]]Sin[d\[Theta]]},{scale[[2]]Cos[d\[Theta]],scale[[1]]Sin[d\[Theta]]}];
dp\[Theta]=ArcTan[pos[[1]],pos[[2]]];
dp\[Theta]+n\[Theta]
]


Attributes[GFX]={HoldAll};
Options[GFX]=Options[Graphics];
GFX[primatives_,opts:OptionsPattern[Graphics]]:=Module[{imgSize,pltRng,out},
imgSize=If[Length[OptionValue[ImageSize]]<2,{OptionValue[ImageSize],OptionValue[ImageSize]},OptionValue[ImageSize]];
SetOptions[AngleScaled,PlotRange->{{0,1},{0,1}},ImageSize->imgSize];
pltRng=plotRange[Graphics[primatives//.{angleScaled->Sequence},ImageSize->imgSize]];
SetOptions[AngleScaled,PlotRange->pltRng,ImageSize->imgSize];
out=Graphics[primatives//.{ angleScaled[x_]:> AngleScaled[x,PlotRange->pltRng,ImageSize->imgSize]},PlotRange->pltRng,ImageSize->imgSize,opts];
out
]


Clear[ellipse];
Options[ellipse]={Resolution-> 100};
ellipse[{xy_, ab_, \[Phi]_},opts:OptionsPattern[ellipse]]:=ellipse[xy, ab, \[Phi],{0,2Pi},"Closed",opts];
ellipse[xy_, ab_, \[Phi]_,{\[Phi]1_,\[Phi]2_},opts:OptionsPattern[ellipse]]:=ellipse[xy, ab, \[Phi],{\[Phi]1,\[Phi]2},"Closed",opts];
ellipse[{xy_, ab_, \[Phi]_},{\[Phi]1_,\[Phi]2_},opts:OptionsPattern[ellipse]]:=ellipse[xy, ab, \[Phi],{\[Phi]1,\[Phi]2},"Closed",opts];
ellipse[{xy_, ab_, \[Phi]_},"Open",opts:OptionsPattern[ellipse]]:=ellipse[xy, ab, \[Phi],{0,2Pi},"Open",opts];
ellipse[xy_, ab_, \[Phi]_,{\[Phi]1_,\[Phi]2_},"Open",opts:OptionsPattern[ellipse]]:=ellipse[xy, ab, \[Phi],{\[Phi]1,\[Phi]2},"Open",opts];
ellipse[{xy_, ab_, \[Phi]_},{\[Phi]1_,\[Phi]2_},"Open",opts:OptionsPattern[ellipse]]:=ellipse[xy, ab, \[Phi],{\[Phi]1,\[Phi]2},"Open",opts];
ellipse[xy_, ab_, \[Phi]_,{\[Phi]1_,\[Phi]2_},"Closed",OptionsPattern[ellipse]]:=Module[{res,fun,pnts,partition},
  res=OptionValue[Resolution];
  fun=paramEllipseFunction[{xy, ab, \[Phi]}];
  pnts=Table[fun[\[Phi]1+k (\[Phi]2-\[Phi]1)/res],{k,0,res}];
  partition=Polygon[{Sequence@@pnts,xy}];
  Return[partition]
]
ellipse[xy_, ab_, \[Phi]_,{\[Phi]1_,\[Phi]2_},"Open",OptionsPattern[ellipse]]:=Module[{res,fun,pnts,partition},
  res=OptionValue[Resolution];
  fun=paramEllipseFunction[{xy, ab, \[Phi]}];
  pnts=Table[fun[\[Phi]1+k (\[Phi]2-\[Phi]1)/res],{k,0,res}];
  Return[{Line[pnts]}]
]


(* ::Subsubsection:: *)
(*Centroids*)


(* ::Text:: *)
(*Point Centroid*)


pntCentroid=Function[{pnts},Total[pnts]/Length[pnts]];

modelPntCentroid[mdl_,xCoords_]:=Module[{mdlPts},
mdlPts=modelToPoints[mdl,xCoords];
pntCentroid[(Flatten[mdlPts,1])]
]


(* ::Text:: *)
(*Line Centroid*)


lineCentroid[pnt_] := Module[{lineCentroidFun, len, totalLen, lineLengthsFun, linesToPnts}, 
   lineCentroidFun = Function[{x1, y1, x2, y2}, {(1/2)*(x1 + x2), (1/2)*(y1 + y2)}]; 
   lineLengthsFun  = Function[{x1, y1, x2, y2}, Sqrt[(x1 - x2)^2 + (y1 - y2)^2]]; totalLen = 0; 
   linesToPnts = Table[len = lineLengthsFun[pnt[[i,1]], pnt[[i,2]], pnt[[i + 1,1]], pnt[[i + 1,2]]]; totalLen = totalLen + len; 
   lineCentroidFun[pnt[[i,1]], pnt[[i,2]], pnt[[i + 1,1]], pnt[[i + 1,2]]]*len, {i, 1, Length[pnt] - 1}]; 
   Total[linesToPnts]/totalLen
]
modelLineCentroid[mdl_, xCoords_] := Module[{mdlPts}, mdlPts = modelToPolygon[mdl, xCoords][[1]]; lineCentroid[mdlPts]]


(* ::Text:: *)
(*Area Centroid*)


areaCentroid=Function[{polygon},RegionCentroid[polygon]];
modelAreaCentroid[mdl_,xCoords_]:=Module[{mdlArea},
mdlArea=modelToPolygon[mdl,xCoords];
RegionCentroid[mdlArea]
]


(* ::Text:: *)
(*Generate Random Polygon Points.*)


SignedArea[p1_,p2_,p3_]:=0.5 (#1[[2]] #2[[1]]-#1[[1]] #2[[2]])&[p2-p1,p3-p1];
IntersectionQ[p1_,p2_,p3_,p4_]:=SignedArea[p1,p2,p3] SignedArea[p1,p2,p4]<0&&SignedArea[p3,p4,p1] SignedArea[p3,p4,p2]<0;
Deintersect[p_]:=Append[p,p[[1]]]//.{s1___,p1_,p2_,s2___,p3_,p4_,s3___}/;IntersectionQ[p1,p2,p3,p4]:>({s1,p1,p3,Sequence@@Reverse@{s2},p2,p4,s3})//Most;


(* ::Text:: *)
(*Visualise Centroid*)


showTranslationPoly[mdlPts_,imgPts_]:=Module[{mpf,posOut,\[Theta]Out},
{posOut,\[Theta]Out}=shapeMatchingMoments[imgPts,mdlPts];
Graphics[{{FaceForm[Yellow],EdgeForm[Directive[Thick,Green]],Polygon[mdlPts]},
{FaceForm[Directive[{Opacity[0.2],Yellow}]],EdgeForm[Directive[Dashed,Green]],Polygon[imgPts]},
{Blue,Point[imgPts]},
{Blue,Point[mdlPts]},
{Blue,Opacity[0.6],Thin,Table[Line[{mdlPts[[i]],mdlPts[[i]]+vecs[[i]]}],{i,1,Length[mdlPts]}]},
{Black,Arrow[{{0,0},posOut}],Text[NumberForm[posOut,3],posOut]}},Frame->True,Background->White,ImageSize->{400,Automatic}]
]


showMomentsPoly[mdlPts_,force_,moment_]:=Module[{pts},
pts=If[Depth[mdlPts]>3,Flatten[mdlPts,1],mdlPts];
Graphics[{{Table[Line[{{0,0},pts[[i]]}],{i,1,Length[pts]}]},
{FaceForm[Directive[{Opacity[0.2],Yellow}]],EdgeForm[Directive[Dashed,Green]],Polygon[mdlPts]},
{Red,Table[{Arrowheads[Min[{0.02,Norm[force[[i]]]/(2(Max[pts[[All,1]]]-Min[pts[[All,1]]]))}]],
Arrow[{pts[[i]],pts[[i]]+force[[i]]}] (* ,Text[Norm[force[[i]]],pts[[i]]+force[[i]]] *)},{i,1,Length[pts]}]},
{Blue,Block[{len=Sqrt[2 moment]},{Arrow[{{0,0},{len,0},{len,moment/len}}],Text[moment,{len,moment/( len)},{0,-1}]}]}},Background->White,ImageSize->{400,Automatic}]
]


(* ::Subsubsection:: *)
(*Graphics*)


Clear[CrossHair]
CrossHair[xy_,sz_:0.2]:=Module[{},({Disk[xy,sz],
{EdgeForm[Black],FaceForm[None],Disk[xy,sz]},
{Black,Line[{xy-sz{Cos[Pi/4],Sin[Pi/4]},xy+sz{Cos[Pi/4],Sin[Pi/4]}}],Line[{xy-sz{Cos[-Pi/4],Sin[-Pi/4]},xy+sz{Cos[-Pi/4],Sin[-Pi/4]}}]}})];


Clear[easySwatch];
easySwatch[spec_List,cols_Integer:1,opts:OptionsPattern[SwatchLegend]]:=Module[{intSpec},
intSpec=Replace[spec,{"Point"->Graphics[Disk[{0, 0}]],"LargePoint"->Graphics[Disk[{0, 0},2]],
"Line"->Graphics[Line[{{0,0},{1,0}}]],"Area"->Graphics[Rectangle[]],"Arrow"->Graphics[{Arrowheads[0.5],Arrow[{{0,0},{1,0}}]}],{c_,w_}:> {c,w,Graphics[Rectangle[]]}},2];
Panel[SwatchLegend[intSpec[[All,2]], intSpec[[All,1]], LegendMarkers->intSpec[[All,3]],
LegendLayout->Function[{pairs},Grid[Partition[Flatten[pairs],2 cols,2 cols,1,{}],Alignment->Left]],opts]]
]


(* ::Subsubsection:: *)
(*Model Functions : Init*)


rotateModel[mdl_,\[Theta]_]:=Module[{trap,R},
R=RotationMatrix[\[Theta] ];
trap=Transpose[R.Transpose[Flatten[mdl[[1]],1]]];
{{trap[[1;;2]],trap[[3;;4]]},{R.mdl[[2,1]],mdl[[2,2]],mdl[[2,3]]+\[Theta]}}
]


translateModel[mdl_,pos_]:=Module[{},
{{{mdl[[1,1,1]]+pos,mdl[[1,1,2]]+pos},{mdl[[1,2,1]]+pos,mdl[[1,2,2]]+pos}},{mdl[[2,1]]+pos,mdl[[2,2]],mdl[[2,3]]}}
]


scaleModel[mdl_,mdlPos_,scale_]:=Module[{mdlX,mdlPosX},
  mdlX  = {scale  mdl[[1]],{scale mdl[[2,1]],scale mdl[[2,2]],mdl[[2,3]]}};
  mdlPosX  = {scale mdlPos[[1]]-{scale/2,scale/2},mdlPos[[2]]};
 {mdlX,mdlPosX}
]
stretchModel[mdl_,mdlPos_,scale_]:=Module[{trapShift,mdlXL,mdlPosXL},
  trapShift=Function[{d},{{{-d,d},{d,d}},{{-d,-d},{d,-d}}}];
  mdlXL = {  mdl[[1]]+trapShift[scale],{ mdl[[2,1]], mdl[[2,2]]+{scale,scale},mdl[[2,3]]}}; 
  mdlPosXL = { mdlPos[[1]],mdlPos[[2]]};
 {mdlXL,mdlPosXL}
]


Clear[modelToDiagram]
modelToDiagram[model_,color_:Blue]:=Module[{trap,elpse,\[Phi]2,\[Phi]1,tmp,tmb},
trap=model[[1]];
elpse=model[[2]];
\[Phi]2=ArcTan[Sequence@@(trap[[1,2]]-elpse[[1]])];
\[Phi]1=ArcTan[Sequence@@(trap[[2,2]]-elpse[[1]])];
{
{EdgeForm[Directive[color,Dashed]],FaceForm[None],
Polygon[Flatten[{trap[[1]],Reverse[trap[[2]]]},1]],
color,Line[trap[[1]]],Line[trap[[2]]]},
{Directive[Dashed,     color],ellipse[elpse,{2Pi/3,-2Pi/3},"Open"],
 Directive[Dashing[{}],color],ellipse[elpse,{\[Phi]1,\[Phi]2},"Open"]},
{Black,PointSize[Large],
Point[elpse[[1]]],Text[Row[{"(",elpse[[1,1]]," ,",elpse[[1,2]],")"}],elpse[[1]],{1.2,1.2}],
Point[Flatten[trap,1]],Table[Text[Row[{"(",Subscript["x", i 10+ j]," ,",Subscript["y", i 10+ j],")"}] ,trap[[i,j]],{-1,2i-3}],{i,1,2},{j,1,2}],
Directive[Dashed,Black],
Line[{elpse[[1]],elpse[[1]]+(elpse[[2,2]]) {Cos[elpse[[3]]+Pi/2],Sin[elpse[[3]]+Pi/2]}}],Text[" b ",elpse[[1]]+(elpse[[2,2]]/2) {Cos[elpse[[3]]+Pi/2],Sin[elpse[[3]]+Pi/2]},{-1,0}],
Line[{elpse[[1]],elpse[[1]]+(elpse[[2,1]]) {Cos[elpse[[3]]],Sin[elpse[[3]]]}}],Text[" a ",elpse[[1]]+(elpse[[2,1]]/2) {Cos[elpse[[3]]],Sin[elpse[[3]]]},{0,-1}]}
}
]


modelToTable[model_] := Module[{trap, elpse, \[Phi]2, \[Phi]1, tmp, tmb, tblColor}, tblColor = {Automatic, LightBlue, LightRed}; 
    trap = {Flatten[model[[1,1]]], Flatten[model[[1,2]]]}; elpse = model[[2]]; 
    Panel[Grid[{{Panel[TableForm[Map[NumberForm[#1, 4, NumberSigns -> {"-", " "}] & , trap, {2}], TableHeadings -> 
           {{Row[{"(", Subscript["x", "1\[EmptyVerySmallSquare]"], ", ", Subscript["y", "1\[EmptyVerySmallSquare]"], ")"}], Row[{"(", Subscript["x", "2\[EmptyVerySmallSquare]"], ", ", Subscript["y", "2\[EmptyVerySmallSquare]"], ")"}]}, 
            {Row[{Subscript["x", "\[EmptyVerySmallSquare]1"]}], Row[{Subscript["y", "\[EmptyVerySmallSquare]1"]}], Row[{Subscript["x", "\[EmptyVerySmallSquare]2"]}], Row[{Subscript["y", "\[EmptyVerySmallSquare]2"]}]}}, 
          TableAlignments -> Center], "Trapesium Coords", Background -> tblColor[[2]]], 
        Panel[Column[{Grid[{{"\[Theta]", NumberForm[elpse[[3]], 5, NumberSigns -> {"-", " "}]}, {"Center", elpse[[1]]}, 
             Sequence @@ Transpose[{{"a", "b"}, (NumberForm[#1, 5, NumberSigns -> {"-", " "}] & ) /@ elpse[[2]]}]}, 
            Dividers -> {{False, True, False}, {False, False, True, False, True}}]}], "Ellipse", Background -> tblColor[[3]]]}}, Alignment -> {Center, Top}], 
     "Model Parameters", Background -> tblColor[[1]]]]


(* ::Subsubsection:: *)
(*Bounding Box; Tip extraction. : Init*)


Clear[pntBoundingBox]
pntBoundingBox[pnts_]:=Module[{},
{{Min[Floor[pnts[[All,1]]]],Max[Ceiling[pnts[[All,1]]]]},{Min[Floor[pnts[[All,2]]]],Max[Ceiling[pnts[[All,2]]]]}}
]


Clear[modelBoundingBox]
modelBoundingBox[{tri_,{center_,{a_,b_},\[Phi]_}},{pos_,\[Theta]_}]:=Module[{pnts},
pnts=modelBoundingPnts[{tri,{center,{a,b},\[Phi]}},{pos,\[Theta]}];
pntBoundingBox[pnts]
]


Clear[modelBoundingPnts]
modelBoundingPnts[{tri_,{{0,0},{a_,b_},\[Phi]_}},{pos_,\[Theta]_}]:=Module[{i,triExtreama,\[Theta]lim,\[Psi],t1,t2,ellipsePnts,t,angles,QAngles,dn,pnts},
triExtreama =Transpose[RotationMatrix[-\[Theta]].Transpose[{tri[[1,1]],tri[[1,2]],tri[[2,1]],tri[[2,2]]}]];
\[Theta]lim=AngleInequality[ArcTan[tri[[2,2,1]],tri[[2,2,2]]]-\[Theta],ArcTan[tri[[1,2,1]],tri[[1,2,2]]]-\[Theta]];
\[Psi]=-(-\[Phi]+\[Theta]);
t1=ArcTan[a Cos[\[Psi]],-b Sin[\[Psi]]];
t2=ArcTan[a Sin[\[Psi]], b Cos[\[Psi]]];
(* t1=ArcTan[-b Tan[\[Psi]]/a]; t2=ArcTan[ b Cot[\[Psi]]/a]; *)
ellipsePnts={
Function[{t},{a Cos[t] Cos[\[Psi]]-b Sin[t] Sin[\[Psi]], b*Sin[t]*Cos[\[Psi]]+a*Cos[t]*Sin[\[Psi]]}][t1],
Function[{t},{a Cos[t] Cos[\[Psi]]-b Sin[t] Sin[\[Psi]], b*Sin[t]*Cos[\[Psi]]+a*Cos[t]*Sin[\[Psi]]}][t2]};
t=Map[ArcTan[#[[1]],#[[2]]]&, ellipsePnts];
angles={t[[1]],t[[2]],t[[1]]+Pi,t[[2]]+Pi};
QAngles=Map[\[Theta]lim, angles];
dn=Flatten[{Pick[Flatten[{ellipsePnts,-ellipsePnts},1], QAngles],triExtreama},1];
Map[(#+pos)&,dn]
];
modelBoundingPnts[{tri_,{center_,{a_,b_},\[Phi]_}},{pos_,\[Theta]_}]:=Module[{mdl,position,pnts},
mdl=translateModel[{tri,{center,{a,b},\[Phi]}},-center];
position={pos+center,\[Theta]};
pnts=modelBoundingPnts[Chop[mdl],position];
pnts
]


Clear[extraBoundingPnts]
extraBoundingPnts[mdl_,mdlPos_]:=Module[{rng, pnts,pntsR},
rng = modelBoundingBox[mdl, {{0,0},0}];
pnts = {{rng[[1,1]], rng[[2,1]]}, {rng[[1,1]], rng[[2,2]]}, {rng[[1,2]], rng[[2,1]]}, {rng[[1,2]], rng[[2,2]]}};
Map[(#+mdlPos[[1]])&,Transpose[RotationMatrix[- mdlPos[[2]]].Transpose[pnts]]]
]


Clear[extraBoundingBox]
extraBoundingBox[mdl_,mdlPos_]:=Module[{rng, pnts,pntsR},
pntBoundingBox[extraBoundingPnts[mdl,mdlPos]]
]


ToCropRot[box:{{x0_,x1_},{y0_,y1_}},\[Theta]_]:=Module[{boxPts,boxShifted,boxShiftedRot,rotShift,cropPts,frame},
boxPts={{x0,y0},{x0,y1},{x1,y1},{x1,y0}};
boxShifted=Map[(#-boxPts[[1]])&,boxPts];
boxShiftedRot=Transpose[RotationMatrix[\[Theta]].Transpose[boxShifted]];
rotShift=-{Min[boxShiftedRot[[All,1]]],Min[boxShiftedRot[[All,2]]]};
cropPts=Map[(#+rotShift)&,boxShiftedRot];
frame={{Min[cropPts[[All,1]]],Max[cropPts[[All,1]]]},{Min[cropPts[[All,2]]],Max[cropPts[[All,2]]]}};
Function[{x,y},Evaluate[RotationMatrix[\[Theta]].({x,y}-boxPts[[1]])+rotShift]]
]


ToCropRot[box:{{x0_,x1_},{y0_,y1_}},\[Theta]_]:=Module[{},
Function[{x$,y$},{(-x0+x$) Cos[\[Theta]]-Min[0,(-x0+x1) Cos[\[Theta]],-(-y0+y1) Sin[\[Theta]],(-x0+x1) Cos[\[Theta]]-(-y0+y1) Sin[\[Theta]]]-(-y0+y$) Sin[\[Theta]],(-y0+y$) Cos[\[Theta]]-Min[0,(-y0+y1) Cos[\[Theta]],(-x0+x1) Sin[\[Theta]],(-y0+y1) Cos[\[Theta]]+(-x0+x1) Sin[\[Theta]]]+(-x0+x$) Sin[\[Theta]]}]
]


Clear[fixImageDimensionRanges]
fixImageDimensionRanges[img_Image,{{x0_,x1_},{y0_,y1_}}]:=Module[{dim,a0,a1,b0,b1},
dim=Reverse[ImageDimensions[img]];
a0=Max[1,Floor[x0]]; a1=Min[dim[[1]],Ceiling[x1]];
b0=Max[1,Floor[y0]]; b1=Min[dim[[2]],Ceiling[y1]];
{{a0,a1},{b0,b1}}
]


Clear[cropTip]
cropTip[img_,model_,modelPos_,rescale_]:=Module[{box,mdl,mdlPos,imgData,toCropRot,cropMdlPos,imgRot,cropBox,cropImgData},
  box=fixImageDimensionRanges[img,modelBoundingBox[model,modelPos] rescale];
  mdl={rescale model[[1]],{rescale model[[2,1]],rescale model[[2,2]],model[[2,3]]}};
  mdlPos={rescale  modelPos[[1]],modelPos[[2]]};
  imgData=ImageData[img][[box[[1,1]];;box[[1,2]],box[[2,1]];;box[[2,2]]]];
  {Image[imgData],mdl,{mdlPos-{box[[1,1]],box[[2,1]]},modelPos[[2]]}}
]


Clear[cropTip]
cropTip[img_,model_,modelPos_,rescale_]:=Module[{extraBox,box,mdl,mdlPos,imgData,toCropRot,cropMdlPos,imgRot,cropBox,cropImgData},
extraBox=fixImageDimensionRanges[img,extraBoundingBox[model,modelPos] rescale];
box=fixImageDimensionRanges[img,modelBoundingBox[model,modelPos] rescale];
mdl={rescale model[[1]],{rescale model[[2,1]],rescale model[[2,2]],model[[2,3]]}};
mdlPos={rescale  modelPos[[1]],modelPos[[2]]};
imgData=ImageData[img][[extraBox[[1,1]];;extraBox[[1,2]],extraBox[[2,1]];;extraBox[[2,2]]]];
toCropRot=ToCropRot[extraBox,modelPos[[2]]];
cropMdlPos=toCropRot[mdlPos[[1,1]],mdlPos[[1,2]]];
imgRot=ImageRotate[Image[imgData],mdlPos[[2]]] ;
cropBox=fixImageDimensionRanges[imgRot,Map[({Ceiling[#[[1]]],Floor[#[[2]]]})&,modelBoundingBox[mdl,{cropMdlPos,0}]]];
cropImgData=ImageData[imgRot][[cropBox[[1,1]];;cropBox[[1,2]],cropBox[[2,1]];;cropBox[[2,2]]]];
{Image[cropImgData],mdl,{cropMdlPos-{cropBox[[1,1]],cropBox[[2,1]]},0}}
]


Clear[tipMask]
tipMask[img_,mdl_,mdlPos_,frame_]:=Module[{},
ImageRotate[Rasterize[Graphics[{{EdgeForm[Black], FaceForm[White], modelToPolygon[mdl, mdlPos]}, 
    {EdgeForm[Red], FaceForm[None], Rectangle[Sequence @@ (#1 - {frame[[1,1]], frame[[2,1]]} & ) /@ Transpose[frame]]}}, 
   Background -> Black, ImagePadding -> None, 
   PlotRangePadding -> None], 
  ImageSize -> ImageDimensions[ImageRotate[img, Pi/2]]], -Pi/2]
]


maskTip[imgIn_,model_,modelPos_,rescale_]:=Module[{img,mdl,mdlPos},
{img,mdl,mdlPos}=cropTip[imgIn, model, modelPos, rescale];
ImageMultiply[ImageRotate[img,Pi/2], tipMask[img,mdl,mdlPos] ]
]
maskTip[img_,mdl_,mdlPos_]:=Module[{},
ImageMultiply[ ImageRotate[img,Pi/2], tipMask[img,mdl,mdlPos] ]
]


(* ::Subsubsection:: *)
(*Dynamic Tracking : Init*)


pntMomentOfInertia[pnts_]:=Module[{},
pnts[[All,1]].pnts[[All,1]]+pnts[[All,2]].pnts[[All,2]]
]


cross=Function[{vec1,vec2},vec1[[1]] vec2[[2]]-vec2[[1]] vec1[[2]]];


vecsNforce[ptsImg_,ptsMdl_]:=Module[{vecs,position,force,ptsImgT,angles,angle},
vecs=ptsImg[[1;;Length[ptsMdl]]]-ptsMdl; 
position=Total[vecs]/Length[vecs];
force=Map[(# -position)&,vecs] ;
{vecs,force}
]


shapeMatchingMoments[ptsImg_,ptsMdl_]:=Module[{vecs,position,force,ptsImgT,angles,angle},
{vecs,force}=vecsNforce[ptsImg,ptsMdl];
ptsImgT=Table[+ptsImg[[i]]-position,{i,1,Length[ptsMdl]}];
angles=Table[VectorAngle[ptsMdl[[i]],ptsImgT[[i]]] ,{i,1,Length[ptsMdl]}];
angle=medianMean[angles,0.8][[1]];
{position,angle}
]


(* ::Subsubsection:: *)
(*Find Tip :Init*)


(* ::Text:: *)
(*Find the Tip*)


findTip[imgSClassified_,dWidth_,mdlD_]:=Module[{
std,fStd,drctn,direction\[Theta],strtPnt,pthToTip,edgPts,rnPts,pop,midDigitPts,reachPts,reachPtsStd,midDigitPtsStd,lm,\[Theta]1,mdl,mdlPts,xCoords,imgPts,pos,\[Theta]},
(* 1. Frame Orientation *)
drctn=frameOrientation[imgSClassified,5];
direction\[Theta]=drctn/.{{0,-1}->Pi/2,{0,1}->-Pi/2,{1,0}->0,{-1,0}-> Pi};
std  = Function[{pts},If[Depth[pts]>2,Transpose["R" . Transpose[pts]],If[Length[pts]==2,"R" . pts,{}]]]/.{"R"->RotationMatrix[ direction\[Theta]]};
fStd = Function[{pts},If[Depth[pts]>2,Transpose["R" . Transpose[pts]],If[Length[pts]==2,"R" . pts,{}]]]/.{"R"->RotationMatrix[-direction\[Theta]]};
(* 2. Find Starting Point *)
strtPnt=findStartingPoint[imgSClassified,5];
(* 3. Find Path to Tip *)
{pthToTip,edgPts,rnPts}=runReach[imgSClassified,strtPnt,drctn,{2,1},True,True,True];
(* 4. Fillament Fill *)
pop=pointOnPath[Reverse[pthToTip],2 dWidth];
{midDigitPts,reachPts}=Block[{fillamentFraction=1/3,numFill},
numFill=Floor[fillamentFraction  Abs[Extract[(pthToTip[[1]]-pthToTip[[-1]]),Position[drctn,1|-1]][[1]]]];
fillamentFill[imgSClassified,{pthToTip[[-1]],pop},drctn,numFill]
];
(* 5. Put into standard orientation. *)
reachPtsStd=Map[std,reachPts,{2}];
midDigitPtsStd=std[midDigitPts];
(* 6. Find the Approximate Orientation *)
lm=LinearModelFit[midDigitPtsStd[[Floor[Length[midDigitPtsStd]/6];;-Floor[Length[midDigitPtsStd]/6]]],x,x];
\[Theta]1=ArcTan[lm["BestFitParameters"][[2]]];
(* 7. Generate model points in Approximate Orientation *)
mdl=rotateModel[mdlD,\[Theta]1];
mdlPts=modelToPoints[mdl,midDigitPtsStd[[All,1]]];
(* 8. Find Pos and Orientation *)
xCoords=midDigitPtsStd[[All,1]];
imgPts={reachPtsStd[[All,1]][[1;;Length[mdlPts[[1]]]]],reachPtsStd[[All,2]][[1;;Length[mdlPts[[2]]]]]};
{pos,\[Theta]}=shapeMatchingMoments[Flatten[imgPts,1],Flatten[mdlPts,1]];
{fStd[RotationMatrix[-\[Theta]1].pos],\[Theta]+direction\[Theta]-\[Theta]1}
]


(* ::Subsubsection:: *)
(*Find Tip :Init*)


(* ::Text:: *)
(*Find the Tip*)


buildModel[img_,csRules_]:=Module[{probFuns,partitionFuns,distroFuns,catagoryFun,imgLCaCb,imgLCaCbPartitioned,imgLCaCbProb,imgLCaCbDataClassified,
imgClassified,direction,startPnt,pathToTip,edgePts,runPts,fillamentFraction=1/3,numFillaments,midFingerPts, extraReachPts,direction\[Theta],toStd,fromStd,
excludeOnFramePos, includePos, tipPos, fingerPos, kinkPos, midLineFit, kink\[Theta], width, pntClassPos, middleQ, lines, model, modelPos},
(* Setup ColorSpace *)
probFuns=setProbFun[csRules];
partitionFuns=setPartitioningFun[csRules];
distroFuns=setDistroFun[csRules];
catagoryFun=RegionClassifier[csRules,qRange->True,Slack->0.1];
(* LCaCb Image *)
imgLCaCb=processImage[ImageData[img,"Byte"],{},{},csRules,Unit->True];
(* LCaCb Partitioned Image *)
imgLCaCbPartitioned=processImage[ImageData[img,"Byte"],{{partitionFuns,{1,2,3}}},{},csRules,Unit->False];
(* LCaCb Probability Image *)
imgLCaCbProb=processImage[ImageData[img,"Byte"],{{partitionFuns,{1,2,3}},{probFuns,{4,5,6}}},{},csRules,Unit->False];
(* LCaCb Classified Image *)
imgLCaCbDataClassified=processImage[ImageData[img,"Byte"],{{catagoryFun,{1,2,3}}},{},csRules,Unit->False];
(* Image Component Analysis *)
(* 1. Frame Orientation *)
imgClassified=imgLCaCbDataClassified[[All,All,4]];
direction=frameOrientation[imgClassified,5];
(* 2. Find Starting Point *)
startPnt=findStartingPoint[imgClassified,5];
(* 3. Find Path to Tip *)
{pathToTip,edgePts,runPts}=runReach[imgClassified,startPnt,direction,{2,1},True,True,True];
(* 4. Fillament Fill *)
numFillaments = Ceiling[fillamentFraction Abs[Extract[(pathToTip[[1]] - pathToTip[[-1]]), Position[direction, 1 | -1]][[1]]]];
{midFingerPts, extraReachPts} = fillamentFill[imgClassified, pathToTip, direction, numFillaments];
(* 5. Prep Midpoints For fit *)
(* 5.1 Standard Orientation *)
direction\[Theta]=direction/.{{0,-1}->Pi/2,{0,1}->-Pi/2,{1,0}->0,{-1,0}-> Pi};
  toStd=Function[{pts},If[Depth[pts]>2,Transpose["R" . Transpose[pts]],If[Length[pts]==2,"R" . pts,{}]]]/.{"R"->RotationMatrix[ direction\[Theta]]};
fromStd=Function[{pts},If[Depth[pts]>2,Transpose["R" . Transpose[pts]],If[Length[pts]==2,"R" . pts,{}]]]/.{"R"->RotationMatrix[-direction\[Theta]]};
(* 5.3. Exclude Points: Edge Points on Frame. *)
excludeOnFramePos=edgePointsOnFramePos[imgClassified, extraReachPts, direction];
includePos=Complement[Table[k,{k,1,Length[extraReachPts]}],excludeOnFramePos];
(* 5.4. Exclude Points: Estimated Tip Position *)
{tipPos, fingerPos}=tipEstimate[extraReachPts, includePos, direction];
(* 6.0. MidLine Fit *)
Block[{fitStd},
  {fitStd, kinkPos} = kinkFit[toStd[midFingerPts], fingerPos, 3];
  midLineFit=fromStd[fitStd];
  ];
middleQ = Length[midLineFit] >= 3;
kink\[Theta] = If[Length[midLineFit]>=3,N[Pi]-VectorAngle[midLineFit[[1]]-midLineFit[[2]],midLineFit[[3]]-midLineFit[[2]]],0];
(* 7.0  Width Estimation and non parallel edge points exclusion. *)
{width, pntClassPos, middleQ, lines}=FindWidths[extraReachPts, midLineFit, toStd, fromStd];
(* 8.0  Model The Tip. *)
{model, modelPos} = findModel[extraReachPts, midFingerPts, midLineFit, pntClassPos, direction\[Theta], toStd, width, EllipseAlignment -> False, EdgeAlignment -> True, MassCentered -> True];
{model, modelPos,width}
]



getChannelEndColors[colorRules_,chn_]:=Module[{toLCaCb, fromLCaCb,\[Mu],CStart,CEnd,pts,min,max,rng,rgbPts},
{toLCaCb, fromLCaCb}=setLCaCb["\[Theta]"]/.colorRules;
\[Mu]=("\[Mu]"/.colorRules);
CStart=ReplacePart[\[Mu],chn->0];
CEnd=ReplacePart[\[Mu],chn->1];
pts={fromLCaCb[CStart],fromLCaCb[CEnd]};
min={Min[pts[[All,1]]],Min[pts[[All,2]]],Min[pts[[All,3]]]};
max={Max[pts[[All,1]]],Max[pts[[All,2]]],Max[pts[[All,3]]]};
rng=max-min;
rgbPts=Map[((#-min)/rng)&,pts]
]
