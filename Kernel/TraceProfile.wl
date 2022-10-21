(* ::Package:: *)

(* ::Chapter::Closed:: *)
(*Begin*)


BeginPackage["WolframAlphaMath`TraceProfile`"];

TraceProfile::usage = "Profile one or more functions during an evaluation of some code.";
TraceProfileData::usage = "";
TraceProfileVerbose::usage = "";

Begin["`Private`"];


(* ::Chapter::Closed:: *)
(*Code*)


(* ::Subsubsection::Closed:: *)
(*TraceProfile*)


SetAttributes[TraceProfile, HoldAllComplete];
Options[TraceProfile] = {MaxItems -> 25, "ShowInOut" -> Automatic, "Verbose" -> False};


TraceProfile[syms:{___Symbol}, code_, opts:OptionsPattern[]] :=
	Block[{$MaxTracePrints, $TotalTracePrints, $InOutPrint, $DownValuePrint},
		$MaxTracePrints = Replace[OptionValue[MaxItems], Except[_Integer?NonNegative] -> 25, {0}];
		$TotalTracePrints = 0;
		$InOutPrint = OptionValue["ShowInOut"];
		$DownValuePrint = TrueQ[OptionValue["Verbose"]];
		$InOutPrint = TrueQ[$InOutPrint] || $InOutPrint === Automatic && $DownValuePrint;
		
		iTraceProfile["Print", syms, code]
	]


(* ::Subsubsection::Closed:: *)
(*TraceProfileData*)


SetAttributes[TraceProfileData, HoldAllComplete];


TraceProfileData[syms:{___Symbol}, code_] :=
	Block[{res, data},
		{res, data} = Reap[iTraceProfile["Sow", syms, code], "$TraceSow"];
		
		{res, First[data, {}]}
	]


(* ::Subsubsection::Closed:: *)
(*TraceProfileVerbose*)


SetAttributes[TraceProfileVerbose, HoldAllComplete];
Options[TraceProfileVerbose] = {MaxItems -> 25};


TraceProfileVerbose[syms:{___Symbol}, code_, opts:OptionsPattern[]] :=
	TraceProfile[syms, code, "Verbose" -> True, opts]


(* ::Subsubsection::Closed:: *)
(*iTraceProfile*)


SetAttributes[iTraceProfile, HoldAllComplete];


iTraceProfile["Print", syms_, code_] /; TrueQ[$InOutPrint] :=
	Block[{$cnt = 1, infunc, outfunc},
		infunc = If[$MaxTracePrints > $TotalTracePrints, Print[Text[Style[Row[{"In ", $cnt, ": "}], $tpfcolor, Bold]], #];$cnt++]&;
		outfunc = (If[$MaxTracePrints > $TotalTracePrints, 
			Print[Text[Style[Row[{"Out ", #2, ": "}], $tpfcolor, Bold]], makeProfileCallGrid[#]];$TotalTracePrints++])&;
		
		iTraceProfile[infunc, outfunc, syms, code]
	]


iTraceProfile["Print", syms_, code_] :=
	Block[{$cnt = 1, infunc, outfunc},
		infunc = Null&;
		outfunc = (If[$MaxTracePrints > $TotalTracePrints, Print[Style["\[RightGuillemet] ", $tpfcolor], makeProfileCallGrid[#]];$TotalTracePrints++])&;
		
		iTraceProfile[infunc, outfunc, syms, code]
	]


iTraceProfile["Sow", syms_, code_] :=
	Block[{infunc, outfunc},
		infunc = Null&;
		outfunc = (Sow[# /. Association[o1___, "Input" -> HoldForm[f_], o2___] :> Association[o1, "Input" -> HoldComplete[f], o2], "$TraceSow"]; #)&;
		
		iTraceProfile[infunc, outfunc, syms, code]
	]


iTraceProfile[in_, out_, syms_List, code_] :=
	iTraceProfile[in, out, #, code]&[pickSymbols[syms]]


iTraceProfile[in_, out_, Hold[syms___], code_] /; TrueQ[$DownValuePrint] :=
	Block[{$DownValuePrint = False},
		downValuePatternTrace[{syms}, iTraceProfile[in, out, Hold[syms], code]]
	]


iTraceProfile[in_, out_, Hold[syms___], code_] :=
	Internal`InheritedBlock[{syms},
		Scan[
			If[MemberQ[Attributes[#], Locked],
				Print["Ignoring ", Unevaluated[#], " since it is locked."],
				Unprotect[#];
				DownValues[#] = Prepend[DownValues[#],
					traceDownValue[in, out, #]
				];
			]&,
			{syms}
		];
		code
	]


(* ::Subsubsection::Closed:: *)
(*downValuePatternTrace*)


SetAttributes[downValuePatternTrace, HoldAll];


downValuePatternTrace[syms_List, code_] :=
	Block[{newsyms},
		newsyms = Unique /@ syms;
		Internal`InheritedBlock[syms,
			MapThread[
				If[!MemberQ[Attributes[#], Locked],
					Unprotect[#];
					DownValues[#] = printDVs[{#, #2}, DownValues[#]];
					Update[#]
				]&,
				{syms, newsyms}
			];
			
			code
		]
	]


SetAttributes[printDVs, HoldFirst];


printDVs[{sym_, newsym_}, dvs_] :=
	With[{
			printdvs = dvs /. (HoldPattern[HoldPattern][lhs_] :> _) :> (HoldPattern[_?(dvPrint[lhs];False)] :> Null),
			newdvs = Replace[dvs, (lhs_ :> rhs_) :> ((lhs /. {sym -> newsym}) :> (rhs /; (firedPrint[];True))), {1}]
		},
			SetAttributes[newsym, Attributes[sym]];
			Options[newsym] = Options[sym];
			DownValues[sym] = {HoldPattern[sym[args___]] :> (newsym[args] /. Riffle[printdvs, newdvs])}
	]


SetAttributes[dvPrint, HoldFirst];


dvPrint[HoldPattern[HoldPattern][lhs_] :> _] := dvPrint[lhs]


dvPrint[expr_] :=
	Block[{Internal`$ContextMarks = False},
		Print[Style[Text["    \[LongDash]\[NegativeThinSpace]\[LongRightArrow]  "], $tpcolor, 10], HoldForm[expr]]
	]


firedPrint[] := Print[Text[Style["         \[LongRightArrow] fired!", $tpfcolor, 14, Bold]]]


(* ::Subsubsection::Closed:: *)
(*pickSymbols*)


SetAttributes[pickSymbols, HoldFirst];


pickSymbols[sym_] := 
	Block[{res},
		res = ToExpression[contextPicker[sym] <> SymbolName[sym], InputForm, Hold];
		If[Context[sym] === "Global`" && !definedQ[sym],
			Remove[sym]
		];
		res
	]


pickSymbols[sym_List] := (Hold @@ pickSymbols /@ Unevaluated[sym])[[All, 1]]


$localContextDisambiguationList = LocalObject["ContextDisambiguationList"];


initializeContextDisambiguationList[] := 
	(
		$KernelSession = AbsoluteTime[];
		If[!FileExistsQ[$localContextDisambiguationList],
			Put[<||>, $localContextDisambiguationList]
		]
	);


initializeContextDisambiguationList[];


importContextDisambiguationList[] := Import[$localContextDisambiguationList]


addToContextDisambiguationList[key_, value_] := 
	With[{data = importContextDisambiguationList[]},
		Put[Join[data, <|key -> value|>], $localContextDisambiguationList]
	]


removeFromContextDisambiguationList[key_] := 
	With[{data = importContextDisambiguationList[]},
		Put[KeyDrop[data, key], $localContextDisambiguationList]
	]


clearContextDisambiguationList[] := (Put[<||>, $localContextDisambiguationList];)


SetAttributes[contextPicker, HoldFirst];


contextPicker[sym_] /; Context[sym] =!= "Global`" := Context[sym]


contextPicker[sym_?definedQ] := Context[sym]


contextPicker[sym_] := 
	Block[{names, res = $Failed},
		names = DeleteCases[Names["*`" <> SymbolName[sym]], SymbolName[sym]];
		Which[
			Length[names] == 1 && ToExpression[First[names], InputForm, definedQ],
				res = Context[Evaluate[First[names]]],
			Length[names] == 0,
				res = Context[sym]
		];
		
		res /; res =!= $Failed
	]


contextPicker[sym_] :=
	Block[{name, cdata, choice, session, newdata},
		name = SymbolName[sym];
		cdata = contextDisambiguationList[name];
		If[!KeyExistsQ[cdata, name],
			{choice, session} = contextPickerDialog[sym];
			If[session =!= None,
				newdata = <|"Context" -> choice, "Time" -> AbsoluteTime[]|>;
				Switch[session,
					"Kernel", AppendTo[newdata, "KernelSession" -> $KernelSession],
					"EOD", AppendTo[newdata, "Expiration" -> AbsoluteTime[Tomorrow]],
					"Week", AppendTo[newdata, "Expiration" -> DatePlus[Now, 7]],
					"Month", AppendTo[newdata, "Expiration" -> DatePlus[Now, 30]]
				];
				addToContextDisambiguationList[name, newdata]
			],
			choice = cdata[name]["Context"]
		];
		choice
	]


SetAttributes[contextDisambiguationList, HoldFirst];


contextDisambiguationList[name_] :=
	Block[{data, ndata},
		data = importContextDisambiguationList[];
		ndata = data[name];
		If[
			Or[
				TrueQ[ndata["KernelSession"] < $KernelSession],
				TrueQ[ndata["Expiration"] < AbsoluteTime[Now]]
			],
			removeFromContextDisambiguationList[name]
		];
		
		importContextDisambiguationList[]
	]


SetAttributes[definedQ, HoldFirst];


definedQ[sym_] := 
	Or[
		System`Private`HasDownCodeQ[sym],
		System`Private`HasOwnCodeQ[sym],
		System`Private`HasUpCodeQ[sym],
		Attributes[sym] =!= {},
		Options[sym] =!= {},
		UnlockedBlock[{sym}, Or[
			Length[DownValues[sym]] > 0,
			Length[OwnValues[sym]] > 0,
			Length[UpValues[sym]] > 0,
			Length[SubValues[sym]] > 0
		]]
	]


SetAttributes[contextPickerDialog, HoldFirst];


contextPickerDialog[sym_] :=
	Block[{contexts, sesslbls, res},
		contexts = DeleteCases[Context /@ Names["*`" <> SymbolName[sym]], "Global`"];
		sesslbls = {None -> "Current evaluation only", "Kernel" -> "Kernel session only", "EOD" -> "Through the end of day",
			"Week" -> "For 7 days", "Month" -> "For 30 days", "Local" -> "Always"};
		
		DynamicModule[{context, session = "Kernel"},
			DialogInput[{
				Grid[{
					{
						Style["Context for " <> SymbolName[sym] <> ":", 16],
						Style["Remember choice:", 16]
					},
					{
						RadioButtonBar[Dynamic[context], contexts, Appearance -> "Vertical"],
						RadioButtonBar[Dynamic[session], sesslbls, Appearance -> "Vertical"]
					}
				}, Alignment -> Top, Spacings -> {2, 2}, Dividers -> {{False, True, False}, False}, FrameStyle -> GrayLevel[.7]],
				DefaultButton[]},
				WindowElements -> {"VerticalScrollBar"},
				WindowTitle -> "Choose Context"
			];
			res = {context, session}
		];
		res
	]


(* ::Subsubsection::Closed:: *)
(*Utilities*)


traceDownValue[in_, out_, sym_] :=
	HoldPattern[sym[e__] /; !TrueQ[$FLAGG[sym]]] :> Block[{$FLAGG, res, cnt},
		$FLAGG[sym] = True;
		cnt = in[HoldForm[sym[e]]];
		
		res = Reap[AbsoluteTiming[MaxMemoryUsed[Sow[sym[e], "traceDownValue"]]], "traceDownValue"];
		res = <|"Input" -> HoldForm[sym[e]], "Result" -> res[[-1, 1, 1]], "Timing" -> res[[1, 1]], "Memory" -> res[[1, -1]]|>;
		
		out[res, cnt];
		
		res["Result"]
	]


makeProfileCallGrid[assoc_] :=
	Grid[
		{
			{"Input", assoc["Input"]},
			{If[TrueQ[$DownValuePrint], Tooltip["Timing"^Style["*", Bold, 11], "Timing affected by verbose output."], "Timing"], assoc["Timing"]},
			{"Memory Used", assoc["Memory"]},
			{"Result", assoc["Result"]}
		}, 
		Alignment -> Left,
		Frame -> All,
		Spacings -> {1, 1}
	]


$tpcolor = RGBColor[1, .73, .55];
$tpfcolor = RGBColor[1, .55, .0];


SetAttributes[Unlock, {HoldAll, Listable}];
Unlock[f_, r__] := Unlock[{f, r}]
Unlock[h_] := (
   AttributeCache[h] = Cases[Attributes[h], Protected|ReadProtected];
   Unprotect[h];
   ClearAttributes[h, {Protected, ReadProtected}];
)


SetAttributes[Lock, {HoldAll, Listable}];
Lock[f_, r__] := Lock[{f, r}]
Lock[h_] := (
   SetAttributes[h, AttributeCache[h]];
   If[!FreeQ[AttributeCache[h], Protected], Protect[h]];
   AttributeCache[h]=.;
)


AttributeCache[_] = {};


(* ::Text:: *)
(*A scoping construct that will unlock symbols.*)


SetAttributes[UnlockedBlock, HoldAll];
UnlockedBlock[syms:{__Symbol}, code_] := Block[{res},
	Unlock[syms];
	res = code;
	Lock[syms];
	res
]
UnlockedBlock[s_Symbol, code_] := UnlockedBlock[{s}, code]


(* ::Chapter::Closed:: *)
(*End*)


End[];
EndPackage[];
