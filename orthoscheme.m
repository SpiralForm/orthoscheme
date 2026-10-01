(* ::Package:: *)

(* ::Subsection:: *)
(*some weighted alphabet algebra:*)


(* ::Subsubsection:: *)
(*cross ratio:*)


cr0[a_,b_,c_,d_]:=-(a-b)(c-d)/((a-d)(b-c))//Factor;
cr[list___]/;(Cases[{list},Except[_Integer]]==={})&&EvenQ[Length[{list}]]:=Product[cr0[\!\(\*SubscriptBox[\(z\), \({list}\[LeftDoubleBracket]1\[RightDoubleBracket]\)]\),\!\(\*SubscriptBox[\(z\), \({list}\[LeftDoubleBracket]i - 1\[RightDoubleBracket]\)]\),\!\(\*SubscriptBox[\(z\), \({list}\[LeftDoubleBracket]i\[RightDoubleBracket]\)]\),\!\(\*SubscriptBox[\(z\), \({list}\[LeftDoubleBracket]i + 1\[RightDoubleBracket]\)]\)]^((-1)^({list}[[1]])),{i,3,Length[{list}]-1,2}];
cr[list___]:=cr[list]/.Subscript[z, i_]:>i;
cr[{list___}]:=cr[list];


crf[list___]:=1/cr[list];


crq[list___]/;EvenQ[Length[{list}]]:=Product[\!\(\*SubscriptBox[\(z\), \({list}[\([i]\)]\)]\)-\!\(\*SubscriptBox[\(z\), \({list}[\([i + 1]\)]\)]\),{i,1,Length[{list}]-1,2}]/(Product[\!\(\*SubscriptBox[\(z\), \({list}[\([i]\)]\)]\)-\!\(\*SubscriptBox[\(z\), \({list}[\([i + 1]\)]\)]\),{i,2,Length[{list}]-2,2}]*(\!\(\*SubscriptBox[\(z\), \({list}[\([1]\)]\)]\)-\!\(\*SubscriptBox[\(z\), \({list}[\([\(-1\)]\)]\)]\)));


(* ::Subsubsection:: *)
(*weighted alphabet algebra:*)


ab[]:=Sequence[];


Joinab[ab1_]:=ab1;
Joinab[ab1_,ab2_]/;MonomialList[ab2]==={ab2}:=Inner[Join,First/@FactorList[ab1],First/@FactorList[ab2],Times]/.Join->Times;
Joinab[ab1_,abpoly_]:=Joinab[ab1,#]&/@MonomialList[abpoly]//Total;


Dotab[i_Integer,j_Integer]:=i j;
Dotab[ab[{phi1_,m1_Integer}],ab[{phi2_,m2_Integer}]]:=ab[{phi1*phi2,m1+m2}];
Dotab[ab[{phi1_,m1_Integer}],ab[{phi2_,m2_Integer},omegas__]]:=ab[{phi1*phi2,m1+m2},omegas];
Dotab[ab1_,ab2_]/;MonomialList[ab2]==={ab2}:=Inner[Dotab,First/@FactorList[ab1],First/@FactorList[ab2],Times];
Dotab[ab1_,abpoly_]:=Dotab[ab1,#]&/@MonomialList[abpoly]//Total;


Qshab[i_Integer,j_Integer]:=i j;
Qshab[]:=Sequence[];
Qshab[ab_]:=ab;
Qshab[ab[omega1_,omegas1___],ab[omega2_,omegas2___]]:=Joinab[ab[omega1],Qshab[ab[omegas1],Joinab[ab[omega2],ab[omegas2]]]]+Joinab[ab[omega2],Qshab[ab[omegas2],Joinab[ab[omega1],ab[omegas1]]]]+Joinab[Dotab[ab[omega1],ab[omega2]],Qshab[ab[omegas1],ab[omegas2]]];
Qshab[ab1_,ab2_]/;MonomialList[ab2]==={ab2}&&MonomialList[ab1]=={ab1}:=Inner[Qshab,First/@FactorList[ab1],First/@FactorList[ab2],Times];
Qshab[abpoly1_,abpoly2_]:=Outer[Qshab,MonomialList[abpoly1],MonomialList[abpoly2]]//Flatten//Total;


(* ::Subsubsection:: *)
(*Arborification:*)


Tarb[a_Integer,b_Integer]:=Sequence[];
Tarb[a_Integer,b_Integer,c_Integer,d_Integer]/;(OddQ/@{a-b,b-c,c-d}//And[##]&@@#&):=If[EvenQ[a],-ab[{cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]],1}],ab[{1/cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]],1}]];
Tarb[list___]/;(#>4&&EvenQ[#]&[Length[{list}]])&&(OddQ/@Table[{list}[[i]]-{list}[[i-1]],{i,2,Length[{list}]}]//And[##]&@@#&):=Block[{fir=First[{list}],las=Last[{list}],len=Length[{list}]},Sum[#[Tarb[fir,{list}[[i]],{list}[[j]],las],Qshab[Tarb[##]&@@({list}[[Range[i]]]),Qshab[Tarb[##]&@@({list}[[Range[i,j]]]),Tarb[##]&@@({list}[[Range[j,Length[{list}]]]])]]]&/@If[EvenQ[fir],{Joinab},{Joinab,Dotab}]//Total,{i,2,len,2},{j,i+1,len-1,2}]];


Tarbinq[a_Integer,b_Integer]:=Sequence[];
Tarbinq[a_Integer,b_Integer,c_Integer,d_Integer]/;(OddQ/@{a-b,b-c,c-d}//And[##]&@@#&):=If[EvenQ[a],-ab[{q[a,b,c,d],1}],ab[{q[b,c,d,a],1}]];
Tarbinq[list___]/;(#>4&&EvenQ[#]&[Length[{list}]])&&(OddQ/@Table[{list}[[i]]-{list}[[i-1]],{i,2,Length[{list}]}]//And[##]&@@#&):=Block[{fir=First[{list}],las=Last[{list}],len=Length[{list}]},Sum[#[Tarbinq[fir,{list}[[i]],{list}[[j]],las],Qshab[Tarbinq[##]&@@({list}[[Range[i]]]),Qshab[Tarbinq[##]&@@({list}[[Range[i,j]]]),Tarbinq[##]&@@({list}[[Range[j,Length[{list}]]]])]]]&/@If[EvenQ[fir],{Joinab},{Joinab,Dotab}]//Total,{i,2,len,2},{j,i+1,len-1,2}]];


q2cr0=q[a_,b_,c_,d_]:>cr0[Subscript[z, a],Subscript[z, b],Subscript[z, c],Subscript[z, d]];


(* ::Subsection:: *)
(*alternating multiple polylogarithm on polygon:*)


(* ::Subsubsection:: *)
(*definition of polylogarithms:*)


Li[ab[omega__]]:=Subscript[Li, ##&@@Last/@{omega}][##]&@@First/@{omega};
Li[-ab[omega__]]:=-Subscript[Li, ##&@@Last/@{omega}][##]&@@First/@{omega};
Li[abpoly_]:=Li[#]&/@MonomialList[abpoly]//Total;


Subscript[NLi, weight__][var__]/;(Length[{weight}]==Length[{var}]):=(-1)^Length[{weight}]*GLi[0,1,Sequence@@Flatten[Table[{Table[0,{weight}[[i]]-1],Product[{var}[[j]],{j,1,i}]},{i,Length[{weight}]}]]];


NGLi[a_,b_]:=1;
NGLi[list__]:=Block[{fir={list}//First,las={list}//Last,wei=Length[{list}]},Integrate[NGLi[Sequence@@Append[Delete[{list},{{-1},{-2}}],Subscript[tt, wei-2]]]/(Subscript[tt, wei-2]-{list}[[wei-1]]),{Subscript[tt, wei-2],fir,las}]]


ALi[ab[omega__]]:=Subscript[ALi, ##&@@Last/@{omega}][##]&@@First/@{omega};
ALi[-ab[omega__]]:=-Subscript[ALi, ##&@@Last/@{omega}][##]&@@First/@{omega};
ALi[abpoly_]:=ALi[#]&/@MonomialList[abpoly]//Total;


Subscript[ALi, weight__][var__]/;Length[{weight}]==Length[{var}]:=Block[{depth=Length@{weight}},(1/2^depth)Sum[Product[Subscript[eps, i],{i,depth}]Subscript[Li, weight][##]&@@Table[Subscript[eps, i]Sqrt[{var}[[i]]],{i,depth}],##]&@@Table[{Subscript[eps, i],{-1,1}},{i,depth}]];


per[poly_]:=LiToG[poly/.Subscript[Li, m__][a__]:>Li[{m},{a}]];


PolylogWeight[li[abseq__]]:=Total[Last/@{abseq}];
PolylogWeight[ali[abseq__]]:=Total[Last/@{abseq}];


PolylogWeight[IH[xseq__]]:=Length[{xseq}]-2;


PolygonWeight[mypg[numseq__]]:=(Length[{numseq}]-2)/2;
PolygonWeight[mypgprod_]:=Block[{mypglist=(FactorList[mypgprod]//#1*#2&@@#&/@#&//Complement[#,{1}]&)/.num_ mypg[seq__]:>Sequence@@Table[mypg[seq],num]},(PolygonWeight/@mypglist//Total)];


(* ::Subsubsection:: *)
(*some polygon algebra:*)


ListShuffle[wd[list___]]:=wd[list];
ListShuffle[wd[list1___],wd[list2___]]:=If[Length[{list1}]==0,{wd[list2]},If[Length[{list2}]==0,{wd[list1]},{Join[wd[{list1}[[1]]],#]&/@ListShuffle[wd@@Delete[{list1},1],wd[list2]],Join[wd[{list2}[[1]]],#]&/@ListShuffle[wd@@Delete[{list2},1],wd[list1]]}//Flatten]];
ListShuffle[wdseq__]/;AllTrue[{wdseq},Head[#]==wd&]&&Length[{wdseq}]>2:=ListShuffle[#,{wdseq}//Last]&/@ListShuffle@@Delete[{wdseq},-1]//Flatten;


FindSubContinuousPolygon[{},mypg[numseq__]]:={{}};
FindSubContinuousPolygon[sizelist_,mypg[numseq__]]/;AllTrue[sizelist,EvenQ[#]&&#>=4&]&&Length[sizelist]>0&&(Total[sizelist-1]+1<=Length[{numseq}]):=Block[{len=Length[sizelist],insertslotlen=Length[{numseq}]-Total[sizelist-2]-1,insertpos,insertposr,ii,jj},insertpos=Subsets[Range[insertslotlen],{len}];insertposr=(Prepend[Delete[Accumulate[sizelist-2],-1],0]+#)&/@insertpos;(Inner[({numseq}[[Range[#1,#1+#2-1]]])&,#,sizelist,List])&/@insertposr]; (* subpolygon with certain even size *)
FindSubContinuousPolygon[mypg[numseq__]]/;Length[{numseq}]<=3:={{}};
FindSubContinuousPolygon[mypg[numseq__]]/;Length[{numseq}]>=4:=Join[{{}},Block[{numlen=Length[{numseq}],endlist,endlists},endlist=Select[Subsets[Range[numlen],{2}],(#[[2]]-#[[1]]>=3)&&OddQ[#[[2]]-#[[1]]]&];(Table[Join[{{numseq}[[endlists[[1]];;endlists[[2]]]]},#]&/@FindSubContinuousPolygon[mypg@@({numseq}[[endlists[[2]];;numlen]])],{endlists,endlist}])//Flatten[#,1]&]] (* subpolygons with general even size *)


FindSubOddokPolygon[{},mypg[numseq__]]:={{}};
FindSubOddokPolygon[sizelist_,mypg[numseq__]]/;AllTrue[sizelist,#>=3&]&&Length[sizelist]>0&&(Total[sizelist-1]+1<=Length[{numseq}]):=Block[{len=Length[sizelist],insertslotlen=Length[{numseq}]-Total[sizelist-2]-1,insertpos,insertposr,ii,jj},insertpos=Subsets[Range[insertslotlen],{len}];insertposr=(Prepend[Delete[Accumulate[sizelist-2],-1],0]+#)&/@insertpos;(Inner[({numseq}[[Range[#1,#1+#2-1]]])&,#,sizelist,List])&/@insertposr]; (* subpolygon with certain odd or even size *)


FindSubOddokPolygon[mypg[numseq__]]/;Length[{numseq}]<=2:={{}};
FindSubOddokPolygon[mypg[numseq__]]/;Length[{numseq}]>=3:=Join[{{}},Block[{numlen=Length[{numseq}],endlist,endlists},endlist=Select[Subsets[Range[numlen],{2}],(#[[2]]-#[[1]]>=2)&];(Table[Join[{{numseq}[[endlists[[1]];;endlists[[2]]]]},#]&/@FindSubOddokPolygon[mypg@@({numseq}[[endlists[[2]];;numlen]])],{endlists,endlist}])//Flatten[#,1]&]] (* subpolygons with general odd or even size *)


FindSubContinuousPolygonFixEnd[sizelist_,mypg[numseq__]]/;AllTrue[sizelist,EvenQ[#]&&#>=4&]:=Block[{netsizelist=Delete[sizelist,{{1},{-1}}],netnumseq=Sequence@@Take[{numseq},{First[sizelist],Length[{numseq}]-Last[sizelist]+1}],len=Length[{numseq}]},Join[{{numseq}[[Range[First@sizelist]]]},#,{{numseq}[[Range[len-Last[sizelist]+1,len]]]}]&/@FindSubContinuousPolygon[netsizelist,mypg[netnumseq]]]
FindSubContinuousPolygonFixEnd[mypg[numseq__]]:=Join[{{}},Block[{numlen=Length[{numseq}],endlist,endlists},endlist=Select[Subsets[Range[numlen],{2}],EvenQ[#[[1]]]&&(OddQ[#[[2]]]&&#[[1]]>=4)&&(Length[{numseq}]-#[[2]]>=3)&];Table[Join[{{numseq}[[1;;First[endlists]]]},#,{{numseq}[[Last[endlists];;numlen]]}]&/@FindSubContinuousPolygon[mypg@@{numseq}[[First[endlists];;Last[endlists]]]],{endlists,endlist}]//Flatten[#,1]&]]; (* subpolygons with certain of general even size and has the same starting and ending as the original polygon *)


(* ::Subsubsection:: *)
(*alternating multiple polylogarithm (with real period) of polygons: coproduct and symbol alphabets:*)


PolygonALiCoproduct[num1_,num2_]/;OddQ[num1-num2]:=wd[mypg[]];
PolygonALiCoproduct[numseq__]/;AllTrue[Table[{numseq}[[i]]-{numseq}[[i-1]],{i,2,Length[{numseq}]}],OddQ]&&Length[{numseq}]>2&&EvenQ[Length[{numseq}]]:=Block[{len=Length[{numseq}],altlist=Select[Join[{First[{numseq}]},#,{Last[{numseq}]}]&/@Subsets[Delete[{numseq},{{-1},{1}}],{2,Length[{numseq}]-2,2}],AllTrue[Table[#[[i]]-#[[i-1]],{i,2,Length[#]}],OddQ]&],altlisti,j},Table[wd[mypg@@altlisti,Times@@(mypg@@#&/@Table[Intersection[{numseq},Range[altlisti[[j]],altlisti[[j+1]]]],{j,Length[altlisti]-1}])/.mypg[ii_,jj_]:>1],{altlisti,altlist}]];(* the final equation on page 62 of Rudenko's paper: \[CapitalDelta]^HH coproduct of ALi[Subscript[T, P]] *)


PolygonALiCoproduct[{weight_},mypg[numseq__]]/;PolygonWeight[mypg@numseq]==weight:={wd[mypg[numseq]]};
PolygonALiCoproduct[weightlist_,mypg[numseq__]]/;(PolygonWeight[mypg[numseq]]==Total[weightlist])&&(Length[weightlist]>=2)&&AllTrue[weightlist,#>0&]:=Block[{lastwei=Last[weightlist],prewei=Delete[weightlist,-1],subpgsizeset=Flatten[Permutations/@IntegerPartitions[Last[weightlist]],1],subpgset,subpgs,word1},subpgset=FindSubContinuousPolygon[2#+2,mypg[numseq]]&/@subpgsizeset//Flatten[#,1]&;word1=Table[wd[mypg@@Complement[{numseq},Flatten[Map[Delete[#,{{1},{-1}}]&,subpgs,1]]],Times@@(mypg@@#&/@subpgs)],{subpgs,subpgset}];
word1/.wd[mypg1_,mypg2_]:>(Join[#,wd[mypg2]]&/@PolygonALiCoproduct[prewei,mypg1])//Flatten];(* the final equation on page 62 of Rudenko's paper: coproduct of ALi[Subscript[T, P]] order by order *)


PolygonALiSym[1]:={wd[]};
PolygonALiSym[mypg[numseq__]]:=PolygonALiSym[numseq];
PolygonALiSym[mypgprod_]:=Block[{mypglist=FactorList[mypgprod]//First/@#&//Complement[#,{1}]&},(Outer[ListShuffle,Sequence@@PolygonALiSym/@mypglist]//Flatten)/;AllTrue[Head/@mypglist,#===mypg&]];
PolygonALiSym[list__]/;(OddQ/@Table[{list}[[i]]-{list}[[i-1]],{i,2,Length[{list}]}]//And[##]&@@#&):=Block[{len=Length[{list}]},If[len<=2,{wd[]},Table[Join[wd[mypg@@({list}[[{1,i,j,len}]])],#]&/@Flatten[Outer[Flatten[Table[ListShuffle[wds,#3],{wds,ListShuffle[#1,#2]}]]&,PolygonALiSym@@({list}[[Range[i]]]),PolygonALiSym@@({list}[[Range[i,j]]]),PolygonALiSym@@({list}[[Range[j,len]]])]],{i,2,len-2,2},{j,i+1,len-1,2}]//Flatten]] (* the final equation on page 62 of Rudenko's paper: full symbol of ALi[Subscript[T, P]] *)


(* ::Subsubsection:: *)
(*real period of ALi of polygon:*)


RePer[mypg[numseq__]]:=Block[{weight=PolygonWeight[mypg[numseq]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1];(Power[-1,If[#[[1]]==0,0,Length[#]-1]]Total[(2Pi)^weight PolygonALiCoproduct[#,mypg[numseq]]]/.wd[sym__]:>wd@@({sym}/(2Pi I)^#)/.wd[bb_,aa___]:>Re[aa//Times]Im[bb]/.{Im[aa_ bb_]:>Re[aa]Im[bb]+Re[bb]Im[aa],Re[cc_ dd_]:>Re[cc]Re[dd]-Im[cc]Im[dd]})&/@par];
ComplexPer[mypg[numseq__]]:=Block[{weight=PolygonWeight[mypg[numseq]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1];(Power[-1,If[#[[1]]==0,0,Length[#]-1]]Total[(2Pi)^weight PolygonALiCoproduct[#,mypg[numseq]]]/.wd[sym__]:>wd@@({sym}/(2Pi I)^#)/.wd[bb_,aa___]:>Re[aa//Times]bb//.{Im[aa_ bb_]:>Re[aa]Im[bb]+Re[bb]Im[aa],Re[cc_ dd_]:>Re[cc]Re[dd]-Im[cc]Im[dd]})&/@par]; (* no shift *)
ComplexPernew[mypg[numseq__]]:=Block[{weight=PolygonWeight[mypg[numseq]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1];((-1)^If[#1[[1]]==0,0,Length[#1]-1] Total[(2 \[Pi])^weight PolygonALiCoproduct[#1,mypg[numseq]]]/. wd[sym__]:>wd@@((1/(2*\[Pi]*I)^#1)({sym}-If[First[#]==1,Join[{-Pi I/2},Table[0,Length[{sym}]-1]],Table[0,Length[{sym}]]]))/. wd[bb_,aa___]:>Re[Times[aa]] bb//. {Im[aa_ bb_]:>Re[aa] Im[bb]+Re[bb] Im[aa],Re[cc_ dd_]:>Re[cc] Re[dd]-Im[cc] Im[dd]}&)/@par] (* trivial shift *)
ComplexPerLorentzreal[mypg[numseq__]]:=Block[{weight=PolygonWeight[mypg[numseq]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1];((-1)^If[#1[[1]]==0,0,Length[#1]-1] Total[(2 \[Pi])^weight PolygonALiCoproduct[#1,mypg[numseq]]]/. wd[sym__]:>wd@@((1/(2*\[Pi]*I)^#1)({sym}-If[First[#]==1,Join[{Sgn[{sym}[[1]]/.mypg->cr]^Log[-1,Sign[{sym}[[1]]/.mypg[0,a_,b_,2weight+1]:>-Subscript[q, a,b]]] Pi I/2},Table[0,Length[{sym}]-1]],Table[0,Length[{sym}]]]))/. {wd[bb_,aa___]:>Times[aa]bb}&)/@par] (* more shift *)
ComplexPerLorentz[mypg[numseq__]]:=Block[{weight=PolygonWeight[mypg[numseq]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1];((-1)^If[#1[[1]]==0,0,Length[#1]-1] Total[(2 \[Pi])^weight PolygonALiCoproduct[#1,mypg[numseq]]]/. wd[sym__]:>wd@@((1/(2*\[Pi]*I)^#1)({sym}-If[First[#]==1,Join[{Sgn[{sym}[[1]]/.mypg->cr](-Sign[{sym}[[1]]/.mypg[0,a_,b_,2weight+1]:>-Subscript[q, a,b]])Pi I/2},Table[0,Length[{sym}]-1]],Table[0,Length[{sym}]]]))/.{ wd[bb_,aa___]:>Times[aa]bb}&)/@par] (* more shift *)


(* ::Subsection:: *)
(*(alternating) multiple polylogarithm:*)


(* ::Subsubsection:: *)
(*symbol alphabets and coproducts for alternating multiple polylogarithm:*)


SubLiabSeries[parentxseries_,zerolistofparent_,subxnumseries_]/;(Length[parentxseries]>=Max[subxnumseries]>=Length[subxnumseries]>=3)&&(First[parentxseries]===0)&&(subxnumseries[[1]]===1)&&(parentxseries[[subxnumseries[[2]]]]=!=0)&&(parentxseries[[Last[subxnumseries]]]=!=0)&&AllTrue[parentxseries[[zerolistofparent]]//Flatten,#===0&]:=Block[{nzlist=Complement[subxnumseries,zerolistofparent],nzlistlen,nzpos},nzlistlen=Length[nzlist];Table[{parentxseries[[nzlist[[nzpos+1]]]]/parentxseries[[nzlist[[nzpos]]]],Position[subxnumseries,nzlist[[nzpos+1]]][[1,1]]-Position[subxnumseries,nzlist[[nzpos]]][[1,1]]},{nzpos,Length[nzlist]-1}]]; (* finding the Subscript[x, I] series in and above (3.5) of Rudenko's paper. *)


DeltaHF[ab[]]:=wd[1,1];
DeltaHF[ab[abseq__]]:=Block[{xlist=FoldList[Times,1,First/@{abseq}],ablen=Length[{abseq}],pglen=Total[Last/@{abseq}]+2,nzlist=Accumulate[Prepend[Last/@{abseq},2]],x0list,subpgsets,subpg},x0list=Fold[Insert[#1,Sequence@@#2]&,Table[0,Last[nzlist]-ablen-1],List[xlist,nzlist]//Transpose];subpgsets=FindSubOddokPolygon[mypg@@Range[2,pglen]];Sum[If[subpg==={},wd[Times@@(IH@@x0list[[#]]&/@subpg),ab[abseq]],Block[{vertlb=Complement[Range[pglen],Map[Delete[#,{{1},{-1}}]&,subpg,{1}]//Flatten],nzvertlb,verti,vertj},nzvertlb=Intersection[nzlist,vertlb];(-1)^(ablen-Length[nzvertlb]+1) wd[Times@@(IH@@x0list[[#]]&/@subpg),{Table[x0list[[nzvertlb[[verti+1]]]]/x0list[[nzvertlb[[verti]]]],{verti,Length[nzvertlb]-1}],Table[Position[vertlb,nzvertlb[[vertj+1]]][[1,1]]-Position[vertlb,nzvertlb[[vertj]]][[1,1]],{vertj,Length[nzvertlb]-1}]}//Transpose//ab@@#&]]],{subpg,subpgsets}]];(* eq.(3.5) of Rudenko's paper: the HF coproduct of weighted alphabets *)


DeltaHH[ali[abseq__]]:=Block[{len=Length[{abseq}],ss},Sum[DeltaHF[ab@@({abseq}[[ss+1;;len]])]/.wd[wd1_,wd2_]:>wd[(ab@@({abseq}[[1;;ss]]))*wd1/.ab->ali,wd2/.ab->ali],{ss,0,len}]] (* Proposition 6.18 of Rudenko's paper: the HH coproduct of weighted alphabets associated with ALi *)


DeltaHs[{weight_},ali[abseq__]]/;PolylogWeight[ali[abseq]]==weight:=wd[ali[abseq]];
DeltaHs[weightlist_,ali[abseq__]]/;(PolylogWeight[ali[abseq]]==Total[weightlist])&&(Length[weightlist]>=2)&&AllTrue[weightlist,#>0&]:=Block[{xlist=FoldList[Times,1,First/@{abseq}],ablen=Length[{abseq}],pglen=Total[Last/@{abseq}]+2,nzlist=Accumulate[Prepend[Last/@{abseq},2]],x0list,lastwei=First[weightlist],prewei=Delete[weightlist,1],subpgsizeset=Flatten[Permutations/@IntegerPartitions[First[weightlist]],1],subpgset,subpgs,word1},x0list=Fold[Insert[#1,Sequence@@#2]&,Table[0,Last[nzlist]-ablen-1],List[xlist,nzlist]//Transpose];subpgset=Select[FindSubOddokPolygon[#+2,mypg@@Range[1,pglen]]&/@subpgsizeset//Flatten[#,1]&,If[First[#[[1]]]==1,MemberQ[nzlist,Last[#[[1]]]],True]&];Sum[Joinab[wd[If[subpgs[[1,1]]===1,ali@@SubLiabSeries[x0list,Complement[Range[pglen],nzlist],subpgs[[1]]],IH@@x0list[[subpgs[[1]]]]]*(Times@@(IH@@x0list[[#]]&/@Delete[subpgs,1]))],#]&/@MonomialList[(-1)^(ablen-Length[#])DeltaHs[prewei,(ali@@#)]&[SubLiabSeries[x0list,Complement[Range[pglen],nzlist],Complement[Range[pglen],Flatten[Map[Delete[#,{{1},{-1}}]&,subpgs,1]]]]]]//Total,{subpgs,subpgset}]];  (* Proposition 6.18 of Rudenko's paper: coproduct of ALi functions order by order *)


(* ::Subsubsection:: *)
(*symbol alphabets and coproducts for general multiple polylogarithms:*)


(* Li functions *)


DeltaHH[li[abseq__]]:=Block[{len=Length[{abseq}],ss},Sum[DeltaHF[ab@@({abseq}[[ss+1;;len]])]/.wd[wd1_,wd2_]:>wd[(ab@@({abseq}[[1;;ss]]))*wd1/.ab->li,wd2/.ab->li],{ss,0,len}]] (* eq.(3.20) of Rudenko paper: the HH coproduct of Li functions *)


DeltaHs[{weight_},li[abseq__]]/;PolylogWeight[li[abseq]]==weight:=wd[li[abseq]];
DeltaHs[weightlist_,li[abseq__]]/;(PolylogWeight[li[abseq]]==Total[weightlist])&&(Length[weightlist]>=2)&&AllTrue[weightlist,#>0&]:=Block[{xlist=FoldList[Times,1,First/@{abseq}],ablen=Length[{abseq}],pglen=Total[Last/@{abseq}]+2,nzlist=Accumulate[Prepend[Last/@{abseq},2]],x0list,lastwei=First[weightlist],prewei=Delete[weightlist,1],subpgsizeset=Flatten[Permutations/@IntegerPartitions[First[weightlist]],1],subpgset,subpgs,word1},x0list=Fold[Insert[#1,Sequence@@#2]&,Table[0,Last[nzlist]-ablen-1],List[xlist,nzlist]//Transpose];subpgset=Select[FindSubOddokPolygon[#+2,mypg@@Range[1,pglen]]&/@subpgsizeset//Flatten[#,1]&,If[First[#[[1]]]==1,MemberQ[nzlist,Last[#[[1]]]],True]&];Sum[Joinab[wd[If[subpgs[[1,1]]===1,li@@SubLiabSeries[x0list,Complement[Range[pglen],nzlist],subpgs[[1]]],IH@@x0list[[subpgs[[1]]]]]*(Times@@(IH@@x0list[[#]]&/@Delete[subpgs,1]))],#]&/@MonomialList[(-1)^(ablen-Length[#])DeltaHs[prewei,(li@@#)]&[SubLiabSeries[x0list,Complement[Range[pglen],nzlist],Complement[Range[pglen],Flatten[Map[Delete[#,{{1},{-1}}]&,subpgs,1]]]]]]//Total,{subpgs,subpgset}]];  (* eq.(3.20) of Rudenko paper: coproduct of Li functions order by order *)


(* Goncharov I functions: *)


IH[x1_,x2_]:=1;


DeltaHH[IH[xseq__]]:=Block[{subpgsets,subpg,xlen=Length[{xseq}]},subpgsets=FindSubOddokPolygon[mypg@@Range[1,xlen]];Sum[If[subpg==={},wd[1,IH[xseq]],Block[{vertlb=Complement[Range[xlen],Map[Delete[#,{{1},{-1}}]&,subpg,{1}]//Flatten]},wd[Times@@(IH@@{xseq}[[#]]&/@subpg),IH@@{xseq}[[vertlb]]]]],{subpg,subpgsets}]]; (* equation (2.5) of Rudenko's paper: the HH coproduct of Goncharov function *)


DeltaHs[{weight_},IH[xseq__]]/;PolylogWeight[IH[xseq]]==weight:=wd[IH[xseq]];
DeltaHs[weightlist_,IH[xseq__]]/;(PolylogWeight[IH[xseq]]==Total[weightlist])&&(Length[weightlist]>=2)&&AllTrue[weightlist,#>0&]:=Block[{subpgset,pglen=Length[{xseq}],subpgsizeset=Flatten[Permutations/@IntegerPartitions[First[weightlist]],1],subpgs,prewei=Delete[weightlist,1]},subpgset=FindSubOddokPolygon[#+2,mypg@@Range[1,pglen]]&/@subpgsizeset//Flatten[#,1]&;Sum[Joinab[wd[Times@@(IH@@{xseq}[[#]]&/@subpgs)],#]&/@MonomialList[DeltaHs[prewei,IH@@{xseq}[[Complement[Range[pglen],Flatten[Map[Delete[#,{{1},{-1}}]&,subpgs,1]]]]]]]//Total,{subpgs,subpgset}]] (* equation (2.5) of Rudenko's paper: coproduct of Goncharov function order by order *)


IH2Li[IH[xseries__]]/;{xseries}[[1]]===0:=If[Last[{xseries}]===0,0,Block[{len=Length[{xseries}],abseries},abseries=SubLiabSeries[{xseries},Position[{xseries},0]//Flatten,Range[len]];(-1)^Length[abseries] li@@abseries]];
IH2Li[IH[xseries__]]/;{xseries}[[1]]=!=0:=IH2Li[IH@@({xseries}-{xseries}[[1]])];
IH2Li[i_Integer IH[xseries__]]:=i IH2Li[IH[xseries]];


Li0ToG[func_]:=func/.Subscript[Li, seq___][vv___]/;Length[{seq}]===Length[{vv}]:>LiToG[Li[{seq},{vv}]]/.Subscript[Li, a_,seq___][vv___]:>(LiToG[Li[{seq},{vv}]]/.G[vvv___,end_]:>G[vvv,Sequence@@Table[0,a],end])
Li1ToG[func_]:=func/.Subscript[Li, seq___][vv___]/;Length[{seq}]===Length[{vv}]:>LiToG[Li[{seq},{vv}]]/.Subscript[Li, a_,seq___][vv___]:>(LiToG[Li[{seq},{vv}]]/.G[vvv___,end_]:>G[Sequence@@({vvv}/end),Sequence@@Table[0,a],1]);


(* ::Subsection:: *)
(*cluster polylogarithm:*)


QLi[n_Integer,mypg_]/;AllTrue[mypg[[2;;]]-mypg[[;;-2]],OddQ]:=Li[Tarb@@mypg]/.Subscript[Li, ns__][cs__]:>Subscript[Li, n,ns][cs]


QeLi[M_,chain_]:=QLi[M,Range[0,Length[chain]-1]]/.Thread[Thread[Subscript[z,Range[0,Length[chain]-1]]]->Thread[Subscript[z,chain]]];
QoLi[M_,chain_]:=QLi[M,Range[Length[chain]]]/.Thread[Thread[Subscript[z,Range[Length[chain]]]]->Thread[Subscript[z,chain]]];
QfLi[M_,chain_]/;AllTrue[chain[[2;;]]-chain[[;;-2]],OddQ]:=QLi[M,chain-1]/.Thread[Thread[Subscript[z,chain-1]]->Thread[Subscript[z,chain]]];


QLiq[n_Integer,mypg_]/;AllTrue[mypg[[2;;]]-mypg[[;;-2]],OddQ]:=Li[Tarbinq@@mypg]/.Subscript[Li, ns__][cs__]:>Subscript[Li, n,ns][cs]


QeLiq[M_,chain_]:=QLiq[M,Range[0,Length[chain]-1]]/.q[seq__]:>q@@({seq}/.Thread[Range[0,Length[chain]-1]->chain]);
QoLiq[M_,chain_]:=QLiq[M,Range[Length[chain]]]/.q[seq__]:>q@@({seq}/.Thread[Range[Length[chain]]->chain]);
QfLiq[M_,chain_]/;AllTrue[chain[[2;;]]-chain[[;;-2]],OddQ]:=QLiq[M,chain-1]/.q[a_,b_,c_,d_]:>q[a+1,b+1,c+1,d+1];


QLisym[Nweight_Integer,mypglist_List]/;EvenQ[Length[mypglist]]&&Nweight>=(Length[mypglist]-2)/2:=Block[{nn=Length[mypglist]/2-1},Sum[(-1)^(nn-Length[subevenpg]-1)QQLi[Nweight-Length[subevenpg]+1,mypglist[[(Join[2subevenpg,2subevenpg+1]//Sort)+1]]],{subevenpg,Select[Subsets[Range[0,nn]],Length[#]>=2&]}]];
QLiid[nnnweight_Integer,NN_Integer]/;NN>=nnnweight+2:=Sum[(-1)^(Total[evensubpglist]+Length[evensubpglist]/2)*QQLisym[nnnweight,evensubpglist],{evensubpglist,Select[Subsets[Range[0,NN]],(Length[#]>=4&&EvenQ[Length@#])&]}];
QLiid[nnnweight_Integer,NNlist_List]/;Length[NNlist]>=nnnweight+3:=QLiid[nnnweight,Length[NNlist]-1]/.QQLisym[ww_,ll_]:>QQLisym[ww,ll/.Thread[Range[0,Length[NNlist]-1]->NNlist]];


Li2I[Subscript[Li, ns__][cs__]]/;Length[{ns}]-Length[{cs}]==1:=Block[{csl=Length[{cs}],nsl=Length[{ns}],cschain=Join[{0},Table[Product[{cs}[[i]],{i,1,j}],{j,0,Length[{cs}]}]],nschain=Table[Table[0,If[i==1,{ns}[[i]],{ns}[[i]]-1]],{i,1,Length[{ns}]}]},(-1)^csl IH@@Flatten[Riffle[cschain,nschain]]];
Li2I[Subscript[Li, ns__][cs__]]/;Length[{ns}]-Length[{cs}]==0:=Li2I[Subscript[Li, 0,ns][cs]];


QLicount[sitem_Integer,weightn_Integer]:=If[weightn==1,Binomial[sitem,4],Sum[Binomial[sitem-1,ii],{ii,3,weightn+1}]];


(* ::Subsection:: *)
(*map between Subscript[M, 0,n+2] configuration and orthoschemes:*)


(* ::Input:: *)
(*(* map of functions as pull back of map of coordinates: *)*)


Ort2Mo[i_Integer,j_Integer,n_Integer]/;(0<i<n+1)&&(0<j<n+1):=If[i<=j,(Subscript[z, 0]-Subscript[z, i])(Subscript[z, j]-Subscript[z, n+1])(Subscript[z, n+1]-Subscript[z, 0]),Ort2Mo[j,i,n]];
Ort2Cur[i_Integer,j_Integer,n_Integer]/;(0<i<n+1)&&(0<j<n+1):=Subscript[Gr, i]/Subscript[Gr, j];
Mo2Cur[mon_,n_Integer]:=mon//.{(Subscript[z, b_]-Subscript[z, a_]):>If[(0<a<n+1)&&(0<b<n+1),(Subscript[z, 0]-Subscript[z, n+1])(Subscript[Gr, a]^2-Subscript[Gr, b]^2)/(Subscript[Gr, a] Subscript[Gr, b]),If[b==0&&0<a<n+1,(Subscript[z, 0]-Subscript[z, n+1])Subscript[Gr, a],If[a==n+1&&0<b<n+1,(Subscript[z, 0]-Subscript[z, n+1])/Subscript[Gr, b],Subscript[z, b]-Subscript[z, a]]]]}; (* Subscript[Gr, a]/Subscript[Gr, b] <-> Subscript[Q, a,b]/\[Sqrt](Subscript[Q, a,a]Subscript[Q, b,b]) and \!\(
\*SubsuperscriptBox[\(Gr\), \(a\), \(2\)]/
\*SubsuperscriptBox[\(Gr\), \(b\), \(2\)]\) <-> \!\(
\*SubsuperscriptBox[\(Q\), \(a, b\), \(2\)]/\((
\*SubscriptBox[\(Q\), \(a, a\)]
\*SubscriptBox[\(Q\), \(b, b\)])\)\) for 0<a<b<n+1 *)


(* ::Subsection:: *)
(*orthoscheme dissection:*)


OrthoQ[mat_]:=SymmetricMatrixQ[mat]&&Block[{len=Length[mat]},And@@Flatten[Table[Factor[mat[[i,j]]mat[[j,k]]]===Factor[mat[[j,j]]mat[[i,k]]],{i,len},{j,i+1,len},{k,j+1,len}]]];
DoubAsymQ[mat_]:=OrthoQ[mat]&&mat[[1,1]]==0&&Last[Last[mat]]==0;
DihedralAnglesCos[mat_]:=Block[{inv=Inverse[mat],len=Length[mat]},Table[inv[[i,j]]/Sqrt[inv[[i,i]]inv[[j,j]]],{i,len},{j,i+1,len}]//Flatten];
IsSphericalSimplex[mat_]:=SymmetricMatrixQ[mat]&&AllTrue[Flatten[Table[mat[[i,j]]^2/(mat[[i,i]]mat[[j,j]]),{i,Length[mat]},{j,Length[mat]}]],0<=#<=1&]&&AllTrue[DihedralAnglesCos[mat],-1<=#<=1&];
DihedralAngles[mat_]:=ArcCos/@DihedralAnglesCos[mat];
IsIdealSimplex[mat_]:=AllTrue[Diagonal[mat],#==0&];


FindFoot[mat_]/;SymmetricMatrixQ[mat]:=Block[{len=Length@mat,qfoot,matft},qfoot=Table[If[i==len,Subscript[Q, ft,i],Subscript[Q, i,ft]],{i,len}]/.Subscript[Q, j_,ft]:>zz mat[[j,len]];matft=Join[mat[[Range[len-1]]],{qfoot}];{qfoot,zz Subscript[Q, ft,len]}/.Solve[Table[Total[matft[[#,ii]]&/@Table[Range[len-1]/.iii->len,{iii,len-1}]//Det/@#&]==Det[matft[[Range[len-1],ii]]],{ii,Subsets[Range[len],{len-1}]}],{zz,Subscript[Q, ft,len]}]]//First;(* gives the list qfoot and Gram elements Subscript[Q, ft,ft] *)


OrthoDsec[Vol[mat_],i_Integer]:=OrthoDsec[sgn[1]Vol[mat],i];
OrthoDsec[sgn[fac_]Vol[mat_],1]/;SymmetricMatrixQ[mat]:=Block[{foot,len=Length[mat]},foot=FindFoot[mat];(Vol/@Table[Insert[Insert[mat,foot[[1]],-2]//Transpose,Insert[Sequence@@foot,-2],-2][[i,i]],{i,Complement[Range[len+1],{#}]&/@Range[len-1]}])*Table[sgn[fac*(Transpose[Insert[mat[[Delete[Range[len-1],i]]],foot[[1]],i]][[Range[len-1]]]//Det)/(mat[[Range[len-1],Range[len-1]]]//Det)],{i,len-1}]];


OrthoDSing[sgn[fac_]Vol[singmat_],i_Integer]/;(i>1):=Block[{len=Length@singmat,bas,foot,foota1},bas=singmat[[Join[Range[len-i],{len}],Join[Range[len-i],{len}]]];foot=FindFoot[bas];foota1=Fold[Insert[#1,#2,-2]&,foot[[1]],Table[singmat[[j,j]]foot[[1,len-i+1]]/singmat[[j,len]],{j,len-i+1,len-1}]];(Vol/@Table[Delete[#,ii]&/@Delete[Insert[Insert[singmat,foota1,len-i+1]//Transpose,Insert[foota1,foot[[2]],len-i+1],len-i+1],ii],{ii,Range[len-i]}])*Table[sgn[fac*(Transpose[Insert[singmat[[Delete[Range[len-i],ii],Join[Range[len-i],{len}]]],foot[[1]],ii]][[Range[len-i]]]//Det)/(singmat[[Range[len-i],Range[len-i]]]//Det)],{ii,len-i}]];
OrthoDsec[sgn[fac_]Vol[mat_],i_Integer]/;i>1:=Flatten[OrthoDSing[#,i]&/@OrthoDsec[sgn[fac]Vol[mat],i-1],1];
OrthoDsec[Vol[mat_]]:=OrthoDsec[Vol[mat],Length[mat]-2];
OrthoDsecVol[Vol[mat_]]:=OrthoDsec[Vol[mat]]/.sgn[__]:>1/.Vol->Join;
OrthoDsecSgn[Vol[mat_]]:=OrthoDsec[Vol[mat]]/.Vol[__]:>1;


Cr2Ort[sgn[fac_]Vol[ortmat_],funx_,n_Integer]/;Dimensions[ortmat]=={n,n}:=sgn[fac]Mo2Cur[funx,n]//.\!\(
\*SubsuperscriptBox[\(Gr\), \(i_\), \(m_\)] :> \(If[EvenQ[m], 
\*SuperscriptBox[\((
\*SuperscriptBox[\(\(Last[ortmat]\)[\([i]\)]\), \(2\)]/ortmat[\([i, i]\)])\), \(m/2\)], 
\*SubsuperscriptBox[\(Gr\), \(i\), \(m\)]]\)\)//.Subscript[q, i_,j_]:>ortmat[[i,j]];
Cr2Ort[Vol[ortmat_],funx_,n_Integer]/;Dimensions[ortmat]=={n,n}:=Mo2Cur[funx,n]//.\!\(
\*SubsuperscriptBox[\(Gr\), \(i_\), \(m_\)] :> \(If[EvenQ[m], 
\*SuperscriptBox[\((
\*SuperscriptBox[\(\(Last[ortmat]\)[\([i]\)]\), \(2\)]/ortmat[\([i, i]\)])\), \(m/2\)], 
\*SubsuperscriptBox[\(Gr\), \(i\), \(m\)]]\)\)//.Subscript[q, i_,j_]:>ortmat[[i,j]];
Cr2Ort[ortmat_,funx_,n_Integer]/;Dimensions[ortmat]=={n,n}:=Cr2Ort[Vol[ortmat],funx,n];


(* ::Subsection:: *)
(*nicer format for symbol alphabet:*)


nice[poly__]/;MonomialList[poly]=!={poly}:=Total[nice/@MonomialList[poly]];
nice[i_Integer]:=i;
nice[CiTi[m__]]:=(Times[Sequence@@#2]CiTi[Sequence@@#1]&[##])&@@Transpose[norm/@{m}];
nice[i_Integer CiTi[m__]]:=i(Times[Sequence@@#2]CiTi[Sequence@@#1]&[##])&@@Transpose[norm/@{m}];
norm[expr_]:=Block[{var=Variables[expr],len,fae=Factor[expr]},len=Length[var];If[IntegerQ[Denominator[fae]]||((Abs[Re[#]]>=1||Im[#]>0)&[fae/.Table[var[[i]]->Prime[i+5],{i,len}]]),{fae,1},{Factor[Denominator[fae]/Numerator[fae]],-1}]];
nicest[wordpoly__]:=FixedPoint[nice[SymbolFactor[#]]&,wordpoly];


(* ::Subsection:: *)
(*the period function:*)


perd[Li[{m__},{c__}]]/;Length[{m}]==Length[{c}]:=Block[{weight=Total[{m}],par=Flatten[Permutations/@IntegerPartitions[Total[{m}]],1]//MapAt[Prepend[#,0]&,#,{1}]&},(2Pi)^weight (Power[-1,If[#[[1]]==0,0,Length[#]-1]]Delta[#,Li[{m},{c}]]/.CT[sym__]:>P@@({sym}/(2Pi I)^#)/.P[aa__,bb_]:>Re[aa//Times]Im[bb]//.{Im[aa_ bb_]:>Re[aa]Im[bb]+Re[bb]Im[aa],Re[cc_ dd_]:>Re[cc]Re[dd]-Im[cc]Im[dd]})&/@par];
perd[Subscript[Li, m__][c__]]:=perd[Li[{m},{c}]];
perr[func__]:=Block[{weight=TranscendentalWeight[per[func]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1]//MapAt[Prepend[#,0]&,#,{1}]&;(2Pi)^weight (Power[-1,If[#[[1]]==0,0,Length[#]-1]]Delta[#,per@func]/.CT[sym__]:>P@@({sym}/(2Pi I)^#)/.P[aa__,bb_]:>Re[aa//Times]Im[bb]//.{Im[aa_ bb_]:>Re[aa]Im[bb]+Re[bb]Im[aa],Re[cc_ dd_]:>Re[cc]Re[dd]-Im[cc]Im[dd]})&/@par];
persv[func__]:=Block[{weight=TranscendentalWeight[per[func]],par},par=Flatten[Permutations/@IntegerPartitions[weight],1]//MapAt[Prepend[#,0]&,#,{1}]&;(2Pi)^weight (Power[-1,If[#[[1]]==0,0,Length[#]-1]]Delta[#,per@func]/.CT[sym__]:>P@@({sym}/(2Pi I)^#)/.P[aa__,bb_]:>Conjugate[aa//Times]Im[bb]//.{Im[aa_ bb_]:>Re[aa]Im[bb]+Re[bb]Im[aa],Re[cc_ dd_]:>Re[cc]Re[dd]-Im[cc]Im[dd],Conjugate[ee_ ff_]:>Conjugate[ee]Conjugate[ff]})&/@par];


(* ::Subsection:: *)
(*representing in classical polylogarithm:*)


CL[Subscript[Li, 1,1][x_,y_]]:=Subscript[Li, 2][(x y-y)/(1-y)]-Subscript[Li, 2][y/(y-1)]-Subscript[Li, 2][x y];
CL[Subscript[Li, 1,1,1][z_,y_,x_]]:=Subscript[Li, 2,1][z (1-y)/(z-1),1/(1-y)]-Subscript[Li, 2,1][z (1-y)/(z-1),(1-x y)/(1-y)]-log[1-x] Subscript[Li, 2][z/(z-1)]-log[1-z]Subscript[Li, 1,1][y,x]
CL[Subscript[Li, 2,1][x_,y_]]:=Subscript[Li, 3][1-x y]+Subscript[Li, 3][1-y]-Subscript[Li, 3][(1-y)/(1-x y)]-Subscript[Li, 3][x]+Subscript[Li, 3][(x-x y)/(1-x y)]-Subscript[Li, 3][1]-log[1-x y](Subscript[Li, 2][1]+Subscript[Li, 2][1-y])-log[(1-y)/(1-x y)]Subscript[Li, 2][x]+1/2log[x]log[1-x y]^2;
CL[Subscript[Li, 1,2][x_,y_]]:=Subscript[Li, 1][x]Subscript[Li, 2][y]-Subscript[Li, 2,1][y,x]-Subscript[Li, 3][x y];
CL[f_Plus]:=CL/@f;


(* ::Subsection:: *)
(*deforming the branch cut:*)


expandlog[exp_]:=Block[{a,b,x,i},exp/. {log[a_]:>Total[(#1[[2]] log[#1[[1]]]&)/@FactorList[a]]}/. {log[i_Integer]->log[Abs[i]],log[a_^x_]:>x log[a]}]/. log[1]->0//. log[a_]:>Block[{var=Variables[a]},If[(a/. Table[var[[i]]->i/(Length[var]+2),{i,Length[var]}])>0,log[a],log[-a]]];


CLAS[funx_]:=Block[{weight=TranscendentalWeight[per[funx/.log[xa_]:>-Subscript[Li, 1][1-xa]/.Subscript[Li, _?IntegerQ][_?IntegerQ]:>1]],symb},symb=MonomialList[Delta[{1,weight-1},funx/.log[xa_]:>-Subscript[Li, 1][1-xa]//per]]/.cc_ CT[aa_,bb_]:>{cc,aa,bb}/.CT[aa_,bb_]:>{1,aa,bb};If[weight<=1,GToLi[funx]/.Li[{1},{aa_}]:>-log[1-aa]/.G->GG/.GG[0,xa_]:>log[xa]//expandlog,funx-Sum[symb[[i,1]]((GToLi[symb[[i,2]]]/.Li[{1},{aa_}]:>-log[1-aa]/.G->GG/.GG[0,xa_]:>log[xa])-(expandlog[GToLi[symb[[i,2]]]/.Li[{1},{aa_}]:>-log[1-aa]/.G->GG/.GG[0,xa_]:>log[xa]]))*CLAS[symb[[i,3]]],{i,Length@symb}]]];


CLD[Subscript[Li, 1,1][x_,y_]]:=CL[Subscript[Li, 1,1][x,y]]//MonomialList//CLAS/@#&//Total;
CLD[Subscript[Li, 2,1][x_,y_]]:=CL[Subscript[Li, 2,1][x,y]]//MonomialList//CLAS/@#&//Total;
CLD[Subscript[Li, 1,2][x_,y_]]:=CL[Subscript[Li, 1,2][x,y]]/.Subscript[Li, 2,1][xx_,yy_]:>CL[Subscript[Li, 2,1][xx,yy]]//MonomialList//CLAS/@#&//Total;
CLD[Subscript[Li, 1,1,1][x_,y_,z_]]:=CL[Subscript[Li, 1,1,1][x,y,z]]/.Subscript[Li, 2,1][xx_,yy_]:>CL[Subscript[Li, 2,1][xx,yy]]/.Subscript[Li, 1,1][xx_,yy_]:>CL[Subscript[Li, 1,1][xx,yy]]//MonomialList//CLAS/@#&//Total;
