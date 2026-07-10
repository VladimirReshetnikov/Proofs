(* Exact recurrence data for OEIS A158415.

   This script uses Wolfram's RootReduce only as an external discovery and
   certificate-generation aid.  The Lean proofs consume the resulting finite
   tables and prove their equalities/inequalities independently.

   Run from src/Lean with:

     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 11 summary
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 11 table
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 11 collisions
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 11 routes
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 12 lean-table
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 12 adjacent
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 12 lean-special
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 12 lean-strict
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 12 lean-range
     wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 15 numeric-lean-membership
*)

ClearAll[
  codeString,
  leanValueExpr,
  leanCodeExpr,
  leanValues15Route,
  printLeanMembership,
  leanRat,
  leanTableTacticName,
  ratBetween,
  ratAbove,
  ratBelow,
  numericRatBetween,
  numericRatAbove,
  numericRatBelow,
  exprValue,
  numericExprValue,
  exprLean,
  indentLines,
  upperProof,
  lowerProof,
  rootKey,
  makeCandidates,
  makeLevel,
  printSummary,
  printTable,
  printCollisions,
  valueIndex,
  printRoutes,
  printLeanTable,
  leanValues14Route,
  leanRatQ,
  certValue,
  certRatAbove,
  certRatBelow,
  intervalCert,
  printLeanIntervalOrderModule,
  monotoneAdjacentQ,
  printAdjacent,
  printLeanSpecial,
  printLeanStrict,
  printLeanRange,
  writeGenerated,
  printLeanBundle
];

$MaxExtraPrecision = 10000;
$MaxRootDegree = 4096;

scriptIndex = FirstPosition[
  StringReplace[ToString /@ $CommandLine, "\\" -> "/"],
  s_String /; StringEndsQ[s, "generate-a158415-data.wl"],
  Missing["NotFound"]
];
scriptArgs = If[ListQ[scriptIndex], Drop[$CommandLine, First[scriptIndex]], {}];

target = Which[
  Environment["A158415_TARGET"] =!= $Failed && Environment["A158415_TARGET"] =!= "",
    ToExpression[Environment["A158415_TARGET"]],
  Length[scriptArgs] >= 1,
    ToExpression[scriptArgs[[1]]],
  True,
    11
];
mode = Which[
  Environment["A158415_MODE"] =!= $Failed && Environment["A158415_MODE"] =!= "",
    Environment["A158415_MODE"],
  Length[scriptArgs] >= 2,
    scriptArgs[[2]],
  True,
    "summary"
];

$numericDiscovery = StringContainsQ[mode, "numeric"];
$numericPrecision = 250;
$numericGroupingTolerance = 10^-90;

If[! IntegerQ[target] || target < 1,
  Print["target must be a positive integer"];
  Exit[2];
];

codeString[{"one"}] := "one";
codeString[{"sqrt", n_Integer, i_Integer}] :=
  "sqrt(" <> ToString[n] <> "," <> ToString[i] <> ")";
codeString[{"add", n1_Integer, i1_Integer, n2_Integer, i2_Integer}] :=
  "add(" <> ToString[n1] <> "," <> ToString[i1] <> "," <>
    ToString[n2] <> "," <> ToString[i2] <> ")";

leanValueExpr[1, 0] := "1";
leanValueExpr[2, 0] := "1";
leanValueExpr[3, 0] := "1";
leanValueExpr[3, 1] := "2";
leanValueExpr[4, 0] := "1";
leanValueExpr[4, 1] := "Real.sqrt 2";
leanValueExpr[4, 2] := "2";
leanValueExpr[n_Integer, i_Integer] /; n >= 5 :=
  "values" <> ToString[n] <> " (" <> ToString[i] <> " : Fin " <>
    ToString[Length[values[n]]] <> ")";

leanCodeExpr[{"one"}] := "1";
leanCodeExpr[{"sqrt", n_Integer, i_Integer}] := "Real.sqrt (" <> leanValueExpr[n, i] <> ")";
leanCodeExpr[{"add", n1_Integer, i1_Integer, n2_Integer, i2_Integer}] :=
  leanValueExpr[n1, i1] <> " + " <> leanValueExpr[n2, i2];

leanTableTacticName[n_Integer] := If[n >= 13, "rfl", "a158415_twelve_table"];

leanRat[r_Rational] :=
  "(" <> ToString[Numerator[r]] <> " / " <> ToString[Denominator[r]] <> " : Real)";
leanRat[n_Integer] := "(" <> ToString[n] <> " : Real)";

leanRatQ[r_Rational] :=
  "(" <> ToString[Numerator[r]] <> " / " <> ToString[Denominator[r]] <> " : Rat)";
leanRatQ[n_Integer] := "(" <> ToString[n] <> " : Rat)";

certValue[code_] := If[$numericDiscovery, numericExprValue[code], exprValue[code]];
certRatAbove[x_, hi_] := If[$numericDiscovery, numericRatAbove[x, hi], ratAbove[x, hi]];
certRatBelow[x_, lo_] := If[$numericDiscovery, numericRatBelow[x, lo], ratBelow[x, lo]];

ratBetween[lo_, hi_] := Module[{den = 1000, r},
  While[True,
    r = (Floor[N[lo, 80] * den] + 1) / den;
    If[lo < r < hi, Return[r]];
    den *= 10;
  ]
];

ratAbove[x_, hi_] := ratBetween[x, hi];

ratBelow[x_, lo_] := Module[{den = 1000, r},
  While[True,
    r = (Ceiling[N[x, 80] * den] - 1) / den;
    If[lo < r < x, Return[r]];
    den *= 10;
  ]
];

numericRatBetween[lo_, hi_] := Module[{den = 1000, r, nlo, nhi},
  nlo = N[lo, $numericPrecision];
  nhi = N[hi, $numericPrecision];
  While[True,
    r = (Floor[nlo * den] + 1) / den;
    If[nlo < N[r, $numericPrecision] < nhi, Return[r]];
    den *= 10;
  ]
];

numericRatAbove[x_, hi_] := numericRatBetween[x, hi];

numericRatBelow[x_, lo_] := Module[{den = 1000, r, nx, nlo},
  nx = N[x, $numericPrecision];
  nlo = N[lo, $numericPrecision];
  While[True,
    r = (Ceiling[nx * den] - 1) / den;
    If[nlo < N[r, $numericPrecision] < nx, Return[r]];
    den *= 10;
  ]
];

exprValue[{"val", n_Integer, i_Integer}] := values[n][[i + 1, 1]];
exprValue[{"one"}] := 1;
exprValue[{"sqrt", n_Integer, i_Integer}] := Sqrt[exprValue[{"val", n, i}]];
exprValue[{"add", n1_Integer, i1_Integer, n2_Integer, i2_Integer}] :=
  exprValue[{"val", n1, i1}] + exprValue[{"val", n2, i2}];

numericExprValue[{"val", n_Integer, i_Integer}] := valueNumbers[n][[i + 1]];
numericExprValue[{"one"}] := N[1, $numericPrecision];
numericExprValue[{"sqrt", n_Integer, i_Integer}] := Sqrt[numericExprValue[{"val", n, i}]];
numericExprValue[{"add", n1_Integer, i1_Integer, n2_Integer, i2_Integer}] :=
  numericExprValue[{"val", n1, i1}] + numericExprValue[{"val", n2, i2}];

exprLean[{"val", n_Integer, i_Integer}] := leanValueExpr[n, i];
exprLean[code_] := leanCodeExpr[code];

rootKey[expr_] := ToString[expr, InputForm];

indentLines[lines_, prefix_String] := prefix <> # & /@ lines;

leanTableSimp :=
  "[values12, values12Nat, values11, values11Nat, values10, values10Nat, " <>
  "values9, values9List, values8, values8List, values7, values7List, " <>
  "values6, values6Nat, values5, values5Nat, rt2_4, rt2_8, rt2_16, rt2_32, " <>
  "rt2_64, rt3_4, rt3_8, rt3_16, sqrt_one_add_sqrt_two, " <>
  "sqrt_sqrt_one_add_sqrt_two, sqrt_sqrt_sqrt_one_add_sqrt_two, " <>
  "sqrt_one_add_rt2_4, sqrt_sqrt_one_add_rt2_4, sqrt_one_add_rt2_8, " <>
  "sqrt_one_add_sqrt_three, sqrt_two_add_sqrt_two, sqrt_four, " <>
  "add_comm, add_assoc, add_left_comm, two_mul]";

values[1] = {{1, {"one"}}};
valueNumbers[1] = {N[1, $numericPrecision]};
candidates[1] = values[1];
groups[1] = List /@ values[1];

makeCandidates[n_Integer] :=
  Join[
    Table[
      {Sqrt[values[n - 1][[i, 1]]], {"sqrt", n - 1, i - 1}},
      {i, Length[values[n - 1]]}
    ],
    Flatten[
      Table[
        Table[
          {
            values[j][[a, 1]] + values[n - 1 - j][[b, 1]],
            {"add", j, a - 1, n - 1 - j, b - 1}
          },
          {a, Length[values[j]]},
          {b, Length[values[n - 1 - j]]}
        ],
        {j, 1, n - 2}
      ],
      2
    ]
  ];

makeLevel[n_Integer] := Module[{cand, reduced, grouped},
  cand = makeCandidates[n];
  candidates[n] = cand;
  If[$numericDiscovery,
    Module[{withNums, sorted, current, groupedNumeric},
      withNums = {#[[1]], #[[2]], N[#[[1]], $numericPrecision]} & /@ cand;
      sorted = SortBy[withNums, #[[3]] &];
      groupedNumeric = {};
      current = {};
      Do[
        If[current === {} ||
            Abs[entry[[3]] - current[[-1, 3]]] <= $numericGroupingTolerance,
          current = Append[current, entry],
          groupedNumeric = Append[groupedNumeric, current];
          current = {entry}
        ],
        {entry, sorted}
      ];
      If[current =!= {}, groupedNumeric = Append[groupedNumeric, current]];
      groups[n] = ({#[[1]], #[[2]]} & /@ #) & /@ groupedNumeric;
      values[n] = {#[[1, 1]], #[[1, 2]]} & /@ groupedNumeric;
      valueNumbers[n] = #[[1, 3]] & /@ groupedNumeric;
    ],
    reduced = {RootReduce[#[[1]]], #[[2]]} & /@ cand;
    grouped = SortBy[
      GatherBy[reduced, rootKey[#[[1]]] &],
      N[#[[1, 1]], 120] &
    ];
    groups[n] = grouped;
    values[n] = #[[1]] & /@ grouped;
    valueKeys[n] = rootKey /@ values[n][[All, 1]];
    valueNumbers[n] = N[values[n][[All, 1]], $numericPrecision];
  ];
];

Do[makeLevel[n], {n, 2, target}];

printSummary[] := Do[
  Print[
    n,
    "\tvalues=", Length[values[n]],
    "\tcandidates=", Length[candidates[n]],
    "\tduplicateGroups=", Count[groups[n], g_ /; Length[g] > 1],
    "\tmaxGroup=", Max[Length /@ groups[n]],
    "\tstrictNumeric=", And @@ Thread[Most[N[values[n][[All, 1]], 120]] < Rest[N[values[n][[All, 1]], 120]]]
  ],
  {n, 1, target}
];

printTable[n_Integer] := Do[
  Print[
    i - 1,
    "\t",
    codeString[values[n][[i, 2]]],
    "\t",
    ToString[values[n][[i, 1]], InputForm],
    "\t",
    ToString[N[values[n][[i, 1]], 40], InputForm]
  ],
  {i, Length[values[n]]}
];

printCollisions[n_Integer] := Module[{dups},
  dups = Select[groups[n], Length[#] > 1 &];
  Print["duplicate groups: ", Length[dups]];
  Do[
    Print[
      i - 1,
      "\t",
      ToString[RootReduce[dups[[i, 1, 1]]], InputForm],
      "\t",
      StringRiffle[codeString /@ dups[[i, All, 2]], " | "]
    ],
    {i, Length[dups]}
  ];
];

valueIndex[n_Integer, expr_] := Module[{reduced, pos, num, diffs, best},
  If[$numericDiscovery,
    num = N[expr, $numericPrecision];
    diffs = Abs[valueNumbers[n] - num];
    best = First[Ordering[diffs, 1]];
    If[diffs[[best]] <= $numericGroupingTolerance, best - 1, Missing["NotFound"]],
    reduced = RootReduce[expr];
    If[! ValueQ[valueKeys[n]],
      valueKeys[n] = rootKey /@ values[n][[All, 1]]
    ];
    pos = FirstPosition[valueKeys[n], rootKey[reduced], Missing["NotFound"]];
    If[ListQ[pos], First[pos] - 1, Missing["NotFound"]]
  ]
];

printRoutes[n_Integer] := Module[{code, idx},
  Do[
    code = candidates[n][[i, 2]];
    idx = valueIndex[n, candidates[n][[i, 1]]];
    Print[codeString[code], "\t", idx],
    {i, Length[candidates[n]]}
  ];
];

leanValues14Route[{"sqrt", 13, i_Integer}] :=
  ".sqrt13 (" <> ToString[i] <> " : Fin 264)";
leanValues14Route[{"add", 1, 0, 12, i_Integer}] :=
  ".oneAdd12 (" <> ToString[i] <> " : Fin 154)";
leanValues14Route[{"add", 4, 1, 9, i_Integer}] :=
  ".sqrtTwoAdd9 (" <> ToString[i] <> " : Fin 33)";
leanValues14Route[{"add", 5, i_Integer, 8, j_Integer}] :=
  ".add5_8 (" <> ToString[i] <> " : Fin 5) (" <> ToString[j] <> " : Fin 20)";
leanValues14Route[{"add", 6, i_Integer, 7, j_Integer}] :=
  ".add6_7 (" <> ToString[i] <> " : Fin 8) (" <> ToString[j] <> " : Fin 13)";
leanValues14Route[code_] := (
  Print["unsupported size-14 route: ", codeString[code]];
  Exit[2]
);

leanValues15Route[{"sqrt", 14, i_Integer}] :=
  ".sqrt14 (" <> ToString[i] <> " : Fin 455)";
leanValues15Route[{"add", 1, 0, 13, i_Integer}] :=
  ".oneAdd13 (" <> ToString[i] <> " : Fin 264)";
leanValues15Route[{"add", 4, 1, 10, i_Integer}] :=
  ".sqrtTwoAdd10 (" <> ToString[i] <> " : Fin 54)";
leanValues15Route[{"add", 5, i_Integer, 9, j_Integer}] :=
  ".add5_9 (" <> ToString[i] <> " : Fin 5) (" <> ToString[j] <> " : Fin 33)";
leanValues15Route[{"add", 6, i_Integer, 8, j_Integer}] :=
  ".add6_8 (" <> ToString[i] <> " : Fin 8) (" <> ToString[j] <> " : Fin 20)";
leanValues15Route[{"add", 7, i_Integer, 7, j_Integer}] :=
  ".add7_7 (" <> ToString[i] <> " : Fin 13) (" <> ToString[j] <> " : Fin 13)";
leanValues15Route[code_] := (
  Print["unsupported size-15 route: ", codeString[code]];
  Exit[2]
);

printLeanTable[n_Integer] := Module[{name},
  If[n === 14,
    Print["inductive Values14Route where"];
    Print["  | sqrt13 (i : Fin 264)"];
    Print["  | oneAdd12 (i : Fin 154)"];
    Print["  | sqrtTwoAdd9 (i : Fin 33)"];
    Print["  | add5_8 (i : Fin 5) (j : Fin 20)"];
    Print["  | add6_7 (i : Fin 8) (j : Fin 13)"];
    Print["  deriving DecidableEq"];
    Print[""];
    Print["namespace Values14Route"];
    Print[""];
    Print["noncomputable def eval : Values14Route -> Real"];
    Print["  | sqrt13 i => Real.sqrt (values13 i)"];
    Print["  | oneAdd12 i => 1 + values12 i"];
    Print["  | sqrtTwoAdd9 i => Real.sqrt 2 + values9 i"];
    Print["  | add5_8 i j => values5 i + values8 j"];
    Print["  | add6_7 i j => values6 i + values7 j"];
    Print[""];
    Print["end Values14Route"];
    Print[""];
    Print["def values14RouteNat : Nat -> Values14Route"];
    Do[
      Print["  | ", i - 1, " => ", leanValues14Route[values[n][[i, 2]]]],
      {i, Length[values[n]]}
    ];
    Print["  | _ => .sqrt13 (0 : Fin 264)"];
    Print[""];
    Print["noncomputable def values14 (i : Fin 455) : Real :="];
    Print["  (values14RouteNat i.1).eval"];
    Return[]
  ];
  If[n === 15,
    Print["inductive Values15Route where"];
    Print["  | sqrt14 (i : Fin 455)"];
    Print["  | oneAdd13 (i : Fin 264)"];
    Print["  | sqrtTwoAdd10 (i : Fin 54)"];
    Print["  | add5_9 (i : Fin 5) (j : Fin 33)"];
    Print["  | add6_8 (i : Fin 8) (j : Fin 20)"];
    Print["  | add7_7 (i j : Fin 13)"];
    Print["  deriving DecidableEq"];
    Print[""];
    Print["namespace Values15Route"];
    Print[""];
    Print["noncomputable def eval : Values15Route -> Real"];
    Print["  | sqrt14 i => Real.sqrt (values14 i)"];
    Print["  | oneAdd13 i => 1 + values13 i"];
    Print["  | sqrtTwoAdd10 i => Real.sqrt 2 + values10 i"];
    Print["  | add5_9 i j => values5 i + values9 j"];
    Print["  | add6_8 i j => values6 i + values8 j"];
    Print["  | add7_7 i j => values7 i + values7 j"];
    Print[""];
    Print["end Values15Route"];
    Print[""];
    Print["def values15RouteNat : Nat -> Values15Route"];
    Do[
      Print["  | ", i - 1, " => ", leanValues15Route[values[n][[i, 2]]]],
      {i, Length[values[n]]}
    ];
    Print["  | _ => .sqrt14 (0 : Fin 455)"];
    Print[""];
    Print["noncomputable def values15 (i : Fin 791) : Real :="];
    Print["  (values15RouteNat i.1).eval"];
    Return[]
  ];
  name = "values" <> ToString[n] <> "Nat";
  Print["noncomputable def ", name, " : Nat -> Real"];
  Do[
    Print["  | ", i - 1, " => ", leanCodeExpr[values[n][[i, 2]]]],
    {i, Length[values[n]]}
  ];
  Print["  | _ => 0"];
];

printLeanMembership[n_Integer] := Module[{},
  If[n === 14,
    Print["/-!"];
    Print["Generated route membership proof for the size-14 table."];
    Print["Regenerate with:"];
    Print["  wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 14 numeric-lean-membership"];
    Print["-/"];
    Print[""];
    Print["namespace Values14Route"];
    Print[""];
    Print["theorem eval_mem_recursiveValueSet_fourteen (route : Values14Route) :"];
    Print["    route.eval \[Element] recursiveValueSet 14 := by"];
    Print["  cases route with"];
    Print["  | sqrt13 i => exact sqrt_values13_mem_recursiveValueSet_fourteen i"];
    Print["  | oneAdd12 i => exact one_add_values12_mem_recursiveValueSet_fourteen i"];
    Print["  | sqrtTwoAdd9 i => exact sqrt_two_add_values9_mem_recursiveValueSet_fourteen i"];
    Print["  | add5_8 i j => exact values5_add_values8_mem_recursiveValueSet_fourteen i j"];
    Print["  | add6_7 i j => exact values6_add_values7_mem_recursiveValueSet_fourteen i j"];
    Print[""];
    Print["end Values14Route"];
    Print[""];
    Print["theorem values14_mem_recursiveValueSet (i : Fin 455) :"];
    Print["    values14 i \[Element] recursiveValueSet 14 := by"];
    Print["  change (values14RouteNat i.1).eval \[Element] recursiveValueSet 14"];
    Print["  exact Values14Route.eval_mem_recursiveValueSet_fourteen (values14RouteNat i.1)"];
    Print[""];
    Print["theorem values14_range_subset_recursiveValueSet_fourteen :"];
    Print["    Set.range values14 \[SubsetEqual] recursiveValueSet 14 := by"];
    Print["  intro x hx"];
    Print["  rcases hx with \:27e8i, rfl\:27e9"];
    Print["  exact values14_mem_recursiveValueSet i"];
    Return[]
  ];
  If[n =!= 15,
    Print["lean-membership is currently implemented only for n = 14 or n = 15"];
    Exit[2]
  ];
  Print["/-!"];
  Print["Generated route membership proof for the size-15 table."];
  Print["Regenerate with:"];
  Print["  wolfram -script Oeis/A158415/computations/wolfram/generate-a158415-data.wl 15 numeric-lean-membership"];
  Print["-/"];
  Print[""];
  Print["namespace Values15Route"];
  Print[""];
  Print["theorem eval_mem_recursiveValueSet_fifteen (route : Values15Route) :"];
  Print["    route.eval \[Element] recursiveValueSet 15 := by"];
  Print["  cases route with"];
  Print["  | sqrt14 i => exact sqrt_values14_mem_recursiveValueSet_fifteen i"];
  Print["  | oneAdd13 i => exact one_add_values13_mem_recursiveValueSet_fifteen i"];
  Print["  | sqrtTwoAdd10 i => exact sqrt_two_add_values10_mem_recursiveValueSet_fifteen i"];
  Print["  | add5_9 i j => exact values5_add_values9_mem_recursiveValueSet_fifteen i j"];
  Print["  | add6_8 i j => exact values6_add_values8_mem_recursiveValueSet_fifteen i j"];
  Print["  | add7_7 i j => exact values7_add_values7_mem_recursiveValueSet_fifteen i j"];
  Print[""];
  Print["end Values15Route"];
  Print[""];
  Print["theorem values15_mem_recursiveValueSet (i : Fin 791) :"];
  Print["    values15 i \[Element] recursiveValueSet 15 := by"];
  Print["  change (values15RouteNat i.1).eval \[Element] recursiveValueSet 15"];
  Print["  exact Values15Route.eval_mem_recursiveValueSet_fifteen (values15RouteNat i.1)"];
  Print[""];
  Print["theorem values15_range_subset_recursiveValueSet_fifteen :"];
  Print["    Set.range values15 \[SubsetEqual] recursiveValueSet 15 := by"];
  Print["  intro x hx"];
  Print["  rcases hx with \:27e8i, rfl\:27e9"];
  Print["  exact values15_mem_recursiveValueSet i"]
];

intervalCert[{"val", n_Integer, i_Integer}, lo_, hi_] :=
  intervalCert[values[n][[i + 1, 2]], lo, hi];
intervalCert[{"one"}, lo_, hi_] :=
  "IntervalCert.one " <> leanRatQ[lo] <> " " <> leanRatQ[hi];
intervalCert[{"sqrt", n_Integer, i_Integer}, lo_, hi_] := Module[
  {x, childLo, childHi},
  x = certValue[{"val", n, i}];
  childLo = certRatBelow[x, lo^2];
  childHi = certRatAbove[x, hi^2];
  "IntervalCert.sqrt " <> leanRatQ[lo] <> " " <> leanRatQ[hi] <>
    " (" <> intervalCert[{"val", n, i}, childLo, childHi] <> ")"
];
intervalCert[{"add", n1_Integer, i1_Integer, n2_Integer, i2_Integer},
    lo_, hi_] := Module[
  {a, b, sum, slackLo, slackHi, alo, ahi, blo, bhi, left, right},
  a = certValue[{"val", n1, i1}];
  b = certValue[{"val", n2, i2}];
  sum = a + b;
  slackLo = sum - lo;
  slackHi = hi - sum;
  alo = certRatBelow[a, a - slackLo/3];
  blo = certRatBelow[b, b - slackLo/3];
  ahi = certRatAbove[a, a + slackHi/3];
  bhi = certRatAbove[b, b + slackHi/3];
  left = intervalCert[{"val", n1, i1}, alo, ahi];
  right = intervalCert[{"val", n2, i2}, blo, bhi];
  "IntervalCert.add " <> leanRatQ[lo] <> " " <> leanRatQ[hi] <>
    " (" <> left <> ") (" <> right <> ")"
];

printLeanIntervalOrderModule[n_Integer] := Module[
  {a, b, av, bv, gap, leftHi, rightLo, rewrites, valueName, titleName,
    tableModule, specials, certName, i},
  If[n =!= 14 && n =!= 15,
    Print["lean-interval-order-module is currently implemented only for n = 14 or n = 15"];
    Exit[2]
  ];
  valueName = "values" <> ToString[n];
  titleName = If[n === 14, "fourteen", "fifteen"];
  tableModule = "A158415" <> If[n === 14, "Fourteen", "Fifteen"] <> "Table";
  Print["import LeanProofs.", tableModule];
  Print["import LeanProofs.A158415IntervalCert"];
  Print[""];
  Print["/-!"];
  Print["# Size-", titleName, " interval order certificates for OEIS A158415"];
  Print[""];
  Print["This generated module replaces the large hand-expanded rational-bound"];
  Print["ladders for the exceptional adjacent comparisons in `", valueName, "` with"];
  Print["compact interval certificates checked by one soundness theorem.  All"];
  Print["rational side conditions are discharged by one batched native decision."];
  Print["-/"];
  Print[""];
  Print["namespace LeanProofs"];
  Print["namespace A158415"];
  Print["namespace Expr"];
  Print[""];
  Print["set_option maxRecDepth 10000"];
  Print["set_option linter.unreachableTactic false"];
  Print["set_option linter.unnecessarySeqFocus false"];
  Print[""];
  specials = Select[
    Range[Length[values[n]] - 1],
    Function[index,
      ! monotoneAdjacentQ[values[n][[index, 2]], values[n][[index + 1, 2]]]
    ]
  ];
  Do[
    i = specials[[k]];
    a = values[n][[i, 2]];
    b = values[n][[i + 1, 2]];
    av = certValue[a];
    bv = certValue[b];
    gap = bv - av;
    leftHi = certRatAbove[av, av + gap/3];
    rightLo = certRatBelow[bv, av + 2 gap/3];
    certName = valueName <> "SpecialCert_" <> ToString[k - 1];
    Print["private def ", certName, " : IntervalCert \[Times] IntervalCert :="];
    Print["  (", intervalCert[a, 0, leftHi], ","];
    Print["    ", intervalCert[b, rightLo, 100], ")"];
    Print[""],
    {k, Length[specials]}
  ];
  Print["private def ", valueName, "SpecialCertNat : Nat -> IntervalCert \[Times] IntervalCert"];
  Do[
    certName = valueName <> "SpecialCert_" <> ToString[k - 1];
    Print["  | ", k - 1, " => ", certName],
    {k, Length[specials]}
  ];
  Print["  | _ => ", valueName, "SpecialCert_0"];
  Print[""];
  Print["private def ", valueName, "SpecialCert (i : Fin ", Length[specials], ") :"];
  Print["    IntervalCert \[Times] IntervalCert :="];
  Print["  ", valueName, "SpecialCertNat i.1"];
  Print[""];
  Print["set_option maxRecDepth 100000 in"];
  Print["set_option maxHeartbeats 0 in"];
  Print["private theorem ", valueName, "SpecialCert_separated :"];
  Print["    \[ForAll] i : Fin ", Length[specials], ","];
  Print["      (", valueName, "SpecialCert i).1.separated (", valueName,
    "SpecialCert i).2 = true := by"];
  Print["  native_decide"];
  Print[""];
  Do[
    i = specials[[k]];
    a = values[n][[i, 2]];
    b = values[n][[i + 1, 2]];
    certName = valueName <> "SpecialCert_" <> ToString[k - 1];
    Print["set_option linter.unusedTactic false in"];
    Print["theorem ", valueName, "_special_", i - 1, " :"];
    Print["    ", valueName, " (", i - 1, " : Fin ", Length[values[n]], ") < ", valueName, " (", i,
      " : Fin ", Length[values[n]], ") := by"];
    Print["  have hcert := ", valueName, "SpecialCert_separated (", k - 1,
      " : Fin ", Length[specials], ")"];
    Print["  change ", certName, ".1.separated ", certName, ".2 = true at hcert"];
    Print["  refine IntervalCert.lt_of_separated ", certName, ".1 ", certName,
      ".2 hcert ?_ ?_"];
    Print["  \[CenterDot] rw [show ", valueName, " (", i - 1, " : Fin ", Length[values[n]], ") = ",
      leanCodeExpr[a], " by rfl]"];
    Print["    simp only [", certName, ", IntervalCert.expr, eval]"];
    rewrites = DeleteDuplicates[highValueRefs[a]];
    Scan[Print["    " <> highValueRewrite[#]] &, rewrites];
    Print["    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf"];
    Print["  \[CenterDot] rw [show ", valueName, " (", i, " : Fin ", Length[values[n]], ") = ",
      leanCodeExpr[b], " by rfl]"];
    Print["    simp only [", certName, ", IntervalCert.expr, eval]"];
    rewrites = DeleteDuplicates[highValueRefs[b]];
    Scan[Print["    " <> highValueRewrite[#]] &, rewrites];
    Print["    a158415_twelve_table <;> try norm_num [sqrt_four] <;> try ring_nf"];
    Print[""],
    {k, Length[specials]}
  ];
  Print["end Expr"];
  Print["end A158415"];
  Print["end LeanProofs"]
];

monotoneAdjacentQ[{"sqrt", n_Integer, i_Integer}, {"sqrt", n_Integer, j_Integer}] :=
  j == i + 1;
monotoneAdjacentQ[{"add", 1, 0, n_Integer, i_Integer},
    {"add", 1, 0, n_Integer, j_Integer}] := j == i + 1;
monotoneAdjacentQ[_, _] := False;

printAdjacent[n_Integer] := Module[{a, b, tag},
  Do[
    a = values[n][[i, 2]];
    b = values[n][[i + 1, 2]];
    tag = If[monotoneAdjacentQ[a, b], "mono", "special"];
    If[tag === "special",
      Print[
        i - 1,
        "\t",
        tag,
        "\t",
        codeString[a],
        "\t",
        codeString[b],
        "\t",
        leanCodeExpr[a],
        "\t",
        leanCodeExpr[b]
      ]
    ],
    {i, Length[values[n]] - 1}
  ];
];

upperProof[{"val", n_Integer, i_Integer}, q_Rational] := Module[{code},
  code = values[n][[i + 1, 2]];
  If[n < 5,
    If[IntegerQ[RootReduce[exprValue[{"val", n, i}]]],
      {"norm_num"},
      upperProof[code, q]
    ],
    Join[
      {"rw [show " <> leanValueExpr[n, i] <> " = " <> exprLean[code] <>
        " by " <> leanTableTacticName[n] <> "]"},
      upperProof[code, q]
    ]
  ]
];
upperProof[{"one"}, q_Rational] := {"norm_num"};
upperProof[{"sqrt", n_Integer, i_Integer}, q_Rational] :=
  If[n < 5 && IntegerQ[RootReduce[exprValue[{"val", n, i}]]],
    {
      "change Real.sqrt (" <> leanValueExpr[n, i] <> ") < " <> leanRat[q],
      "rw [Real.sqrt_lt' (by norm_num : (0 : Real) < " <> leanRat[q] <> ")]",
      "norm_num"
    },
    Join[
      {
        "change Real.sqrt (" <> leanValueExpr[n, i] <> ") < " <> leanRat[q],
        "rw [Real.sqrt_lt' (by norm_num : (0 : Real) < " <> leanRat[q] <> ")]",
        "norm_num",
        "change " <> leanValueExpr[n, i] <> " < " <> leanRat[q^2]
      },
      upperProof[{"val", n, i}, q^2]
    ]
  ];
upperProof[{"add", n1_Integer, i1_Integer, n2_Integer, i2_Integer}, q_Rational] :=
  Module[{a, b, slack, qa, qb, h1, h2},
    a = exprValue[{"val", n1, i1}];
    b = exprValue[{"val", n2, i2}];
    If[$numericDiscovery,
      a = numericExprValue[{"val", n1, i1}];
      b = numericExprValue[{"val", n2, i2}];
      slack = N[q, $numericPrecision] - (a + b);
      qa = numericRatAbove[a, a + slack/3];
      qb = numericRatAbove[b, b + slack/3],
      slack = q - RootReduce[a + b];
      qa = ratAbove[a, a + slack/3];
      qb = ratAbove[b, b + slack/3]
    ];
    h1 = "h" <> ToString[++proofCounter];
    h2 = "h" <> ToString[++proofCounter];
    Join[
      {"change " <> leanValueExpr[n1, i1] <> " + " <> leanValueExpr[n2, i2] <>
        " < " <> leanRat[q]},
      {"have " <> h1 <> " : " <> leanValueExpr[n1, i1] <> " < " <> leanRat[qa] <> " := by"},
      indentLines[upperProof[{"val", n1, i1}, qa], "  "],
      {"have " <> h2 <> " : " <> leanValueExpr[n2, i2] <> " < " <> leanRat[qb] <> " := by"},
      indentLines[upperProof[{"val", n2, i2}, qb], "  "],
      {"linarith"}
    ]
  ];

lowerProof[{"val", n_Integer, i_Integer}, q_Rational] := Module[{code},
  code = values[n][[i + 1, 2]];
  If[n < 5,
    If[IntegerQ[RootReduce[exprValue[{"val", n, i}]]],
      {"norm_num"},
      lowerProof[code, q]
    ],
    Join[
      {"rw [show " <> leanValueExpr[n, i] <> " = " <> exprLean[code] <>
        " by " <> leanTableTacticName[n] <> "]"},
      lowerProof[code, q]
    ]
  ]
];
lowerProof[{"one"}, q_Rational] := {"norm_num"};
lowerProof[{"sqrt", n_Integer, i_Integer}, q_Rational] :=
  If[n < 5 && IntegerQ[RootReduce[exprValue[{"val", n, i}]]],
    {
      "change " <> leanRat[q] <> " < Real.sqrt (" <> leanValueExpr[n, i] <> ")",
      "apply Real.lt_sqrt_of_sq_lt",
      "norm_num"
    },
    Join[
      {
        "change " <> leanRat[q] <> " < Real.sqrt (" <> leanValueExpr[n, i] <> ")",
        "apply Real.lt_sqrt_of_sq_lt",
        "norm_num",
        "change " <> leanRat[q^2] <> " < " <> leanValueExpr[n, i]
      },
      lowerProof[{"val", n, i}, q^2]
    ]
  ];
lowerProof[{"add", n1_Integer, i1_Integer, n2_Integer, i2_Integer}, q_Rational] :=
  Module[{a, b, slack, qa, qb, h1, h2},
    a = exprValue[{"val", n1, i1}];
    b = exprValue[{"val", n2, i2}];
    If[$numericDiscovery,
      a = numericExprValue[{"val", n1, i1}];
      b = numericExprValue[{"val", n2, i2}];
      slack = (a + b) - N[q, $numericPrecision];
      qa = numericRatBelow[a, a - slack/3];
      qb = numericRatBelow[b, b - slack/3],
      slack = RootReduce[a + b] - q;
      qa = ratBelow[a, a - slack/3];
      qb = ratBelow[b, b - slack/3]
    ];
    h1 = "h" <> ToString[++proofCounter];
    h2 = "h" <> ToString[++proofCounter];
    Join[
      {"change " <> leanRat[q] <> " < " <> leanValueExpr[n1, i1] <> " + " <>
        leanValueExpr[n2, i2]},
      {"have " <> h1 <> " : " <> leanRat[qa] <> " < " <> leanValueExpr[n1, i1] <> " := by"},
      indentLines[lowerProof[{"val", n1, i1}, qa], "  "],
      {"have " <> h2 <> " : " <> leanRat[qb] <> " < " <> leanValueExpr[n2, i2] <> " := by"},
      indentLines[lowerProof[{"val", n2, i2}, qb], "  "],
      {"linarith"}
    ]
  ];

printLeanSpecial[n_Integer] := Module[{a, b, q, lhs, rhs},
  Do[
    a = values[n][[i, 2]];
    b = values[n][[i + 1, 2]];
    If[! monotoneAdjacentQ[a, b],
      q = If[$numericDiscovery,
        numericRatBetween[numericExprValue[a], numericExprValue[b]],
        ratBetween[exprValue[a], exprValue[b]]
      ];
      lhs = "values" <> ToString[n] <> " (" <> ToString[i - 1] <> " : Fin " <>
        ToString[Length[values[n]]] <> ")";
      rhs = "values" <> ToString[n] <> " (" <> ToString[i] <> " : Fin " <>
        ToString[Length[values[n]]] <> ")";
      proofCounter = 0;
      Print["set_option linter.unusedTactic false in"];
      Print["theorem values", n, "_special_", i - 1, " :"];
      Print["    ", lhs, " < ", rhs, " := by"];
      Print["  have hleft : ", lhs, " < ", leanRat[q], " := by"];
      Scan[Print["    " <> #] &, upperProof[{"val", n, i - 1}, q]];
      Print["  have hright : ", leanRat[q], " < ", rhs, " := by"];
      Scan[Print["    " <> #] &, lowerProof[{"val", n, i}, q]];
      Print["  linarith"];
      Print[""]
    ],
    {i, Length[values[n]] - 1}
  ];
];

printLeanStrict[n_Integer] := Module[{a, b, i1, i2, sqrtN, addN, addLen},
  sqrtN = n - 1;
  addN = n - 2;
  addLen = Length[values[addN]];
  Print["macro \"values", n, "_sqrt_run\" : tactic =>"];
  Print["  `(tactic| exact sqrt_values", sqrtN, "_strictMono (by decide))"];
  Print[""];
  Print["macro \"values", n, "_one_add_run\" i:num j:num : tactic =>"];
  Print["  `(tactic|"];
  Print["    (change 1 + values", addN, " ($i : Fin ", addLen, ") < 1 + values",
    addN, " ($j : Fin ", addLen, ");"];
  Print["      exact add_lt_add_right"];
  Print["        (values", addN, "_strictMono"];
  Print["          (by decide : ($i : Fin ", addLen, ") < ($j : Fin ", addLen, "))) 1))"];
  Print[""];
  Print["set_option maxHeartbeats 2000000 in"];
  Print["theorem values", n, "_strictMono : StrictMono values", n, " := by"];
  Print["  rw [Fin.strictMono_iff_lt_succ]"];
  Print["  intro i"];
  Print["  fin_cases i"];
  Do[
    a = values[n][[i, 2]];
    b = values[n][[i + 1, 2]];
    Which[
      ! monotoneAdjacentQ[a, b],
        Print["  next => exact values", n, "_special_", i - 1],
      MatchQ[a, {"sqrt", sqrtN, _Integer}] && MatchQ[b, {"sqrt", sqrtN, _Integer}],
        Print["  next => values", n, "_sqrt_run"],
      MatchQ[a, {"add", 1, 0, addN, _Integer}] &&
          MatchQ[b, {"add", 1, 0, addN, _Integer}],
        i1 = a[[5]];
        i2 = b[[5]];
        Print["  next => values", n, "_one_add_run ", i1, " ", i2],
      True,
        Print["  next => fail \"unsupported adjacent pair: ", codeString[a], " < ", codeString[b], "\""]
    ],
    {i, Length[values[n]] - 1}
  ];
];

printUnaryRangeLemma[name_String, binder_String, body_String, len_Integer, codeFn_] := Module[
  {code, idx},
  Print["set_option linter.unusedTactic false in"];
  Print["set_option maxHeartbeats 4000000 in"];
  Print["theorem ", name, " (i : Fin ", len, ") :"];
  Print["    ", body, " \[Element] Set.range values12 := by"];
  Print["  fin_cases i"];
  Do[
    code = codeFn[i - 1];
    idx = valueIndex[12, exprValue[code]];
    If[! IntegerQ[idx],
      Print["  \[CenterDot] fail \"missing value index for ", codeString[code], "\""],
      If[idx === 86 && code =!= values[12][[idx + 1, 2]],
        Print["  \[CenterDot] exact \:27e8(", idx, " : Fin 154), by a158415_twelve_table; rw [sqrt_four]\:27e9"],
        Print["  \[CenterDot] exact \:27e8(", idx, " : Fin 154), by a158415_twelve_table\:27e9"]
      ]
    ],
    {i, len}
  ];
  Print[""]
];

printBinaryRangeLemma[name_String, len1_Integer, len2_Integer, body_String, codeFn_] := Module[
  {code, idx},
  Print["set_option linter.unusedTactic false in"];
  Print["set_option maxHeartbeats 4000000 in"];
  Print["theorem ", name, " (i : Fin ", len1, ") (j : Fin ", len2, ") :"];
  Print["    ", body, " \[Element] Set.range values12 := by"];
  Print["  fin_cases i <;> fin_cases j"];
  Do[
    code = codeFn[i - 1, j - 1];
    idx = valueIndex[12, exprValue[code]];
    If[! IntegerQ[idx],
      Print["  \[CenterDot] fail \"missing value index for ", codeString[code], "\""],
      If[idx === 86 && code =!= values[12][[idx + 1, 2]],
        Print["  \[CenterDot] exact \:27e8(", idx, " : Fin 154), by a158415_twelve_table; rw [sqrt_four]\:27e9"],
        Print["  \[CenterDot] exact \:27e8(", idx, " : Fin 154), by a158415_twelve_table\:27e9"]
      ]
    ],
    {i, len1}, {j, len2}
  ];
  Print[""]
];

highValueRefThreshold[] := If[target >= 15, 10, 13];

highValueRefs[{"one"}] := {};
highValueRefs[{"sqrt", n_Integer, i_Integer}] :=
  If[n >= highValueRefThreshold[],
    Join[{{n, i}}, highValueRefs[values[n][[i + 1, 2]]]],
    {}
  ];
highValueRefs[{"add", n1_Integer, i1_Integer, n2_Integer, i2_Integer}] :=
  Join[
    If[n1 >= highValueRefThreshold[], Join[{{n1, i1}}, highValueRefs[values[n1][[i1 + 1, 2]]]], {}],
    If[n2 >= highValueRefThreshold[], Join[{{n2, i2}}, highValueRefs[values[n2][[i2 + 1, 2]]]], {}]
  ];

highValueRewrite[{n_Integer, i_Integer}] :=
  "rw [show " <> leanValueExpr[n, i] <> " = " <>
    leanCodeExpr[values[n][[i + 1, 2]]] <> " by rfl]";

rangeIndex[targetN_Integer, code_] :=
  valueIndex[targetN, exprValue[code]];

rangeCaseExactQ[targetN_Integer, code_] := Module[{idx, rep, body},
  idx = valueIndex[targetN, exprValue[code]];
  If[! IntegerQ[idx],
    False,
    rep = leanCodeExpr[values[targetN][[idx + 1, 2]]];
    body = leanCodeExpr[code];
    rep === body
  ]
];

rangeCaseEqualityProof[targetN_Integer, code_] := Module[{idx, repCode, rep, body, rewrites},
  idx = valueIndex[targetN, exprValue[code]];
  If[! IntegerQ[idx],
    {"fail \"missing value index for " <> codeString[code] <> "\""},
    repCode = values[targetN][[idx + 1, 2]];
    rep = leanCodeExpr[repCode];
    body = leanCodeExpr[code];
    If[rep === body,
      {
        "change " <> rep <> " = " <> body,
        "rfl"
      },
      rewrites = DeleteDuplicates[Join[highValueRefs[repCode], highValueRefs[code]]];
      {
        "change " <> rep <> " = " <> body,
        Sequence @@ (highValueRewrite /@ rewrites),
        "a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num"
      }
    ]
  ]
];

rangeIndexNatName[name_String] := name <> "_indexNat";
rangeIndexName[name_String] := name <> "_index";
rangeIndexSpecName[name_String] := name <> "_index_spec";

printUnaryRangeLemmaFor[targetN_Integer, name_String, len_Integer, body_String, codeFn_] := Module[
  {allExact, code, compactRouteQ, exactCases, exceptionalCase, exceptionalCases,
   idx, lines, indexNatName, indexName, routeCtor, routeSpecName, specName,
   targetLen},
  targetLen = Length[values[targetN]];
  indexNatName = rangeIndexNatName[name];
  indexName = rangeIndexName[name];
  specName = rangeIndexSpecName[name];
  Print["def ", indexNatName, " : Nat -> Nat"];
  Do[
    code = codeFn[i - 1];
    idx = rangeIndex[targetN, code];
    If[! IntegerQ[idx],
      Print["  | ", i - 1, " => 0 -- missing value index for ", codeString[code]],
      Print["  | ", i - 1, " => ", idx]
    ],
    {i, len}
  ];
  Print["  | _ => 0"];
  Print[""];
  Print["def ", indexName, " (i : Fin ", len, ") : Fin ", targetLen, " :="];
  Print["  Fin.ofNat ", targetLen, " (", indexNatName, " i.1)"];
  Print[""];
  exactCases = If[targetN >= 14,
    Table[rangeCaseExactQ[targetN, codeFn[i - 1]], {i, len}],
    {}
  ];
  exceptionalCases = Flatten[Position[exactCases, False]] - 1;
  allExact = Length[exactCases] === len && exceptionalCases === {};
  routeCtor = Which[
    targetN === 14 && MatchQ[codeFn[0], {"sqrt", 13, 0}],
      "Values14Route.sqrt13",
    targetN === 14 && MatchQ[codeFn[0], {"add", 1, 0, 12, 0}],
      "Values14Route.oneAdd12",
    targetN === 15 && MatchQ[codeFn[0], {"sqrt", 14, 0}],
      "Values15Route.sqrt14",
    targetN === 15 && MatchQ[codeFn[0], {"add", 1, 0, 13, 0}],
      "Values15Route.oneAdd13",
    True,
      None
  ];
  compactRouteQ = StringQ[routeCtor] && Length[exceptionalCases] <= 1;
  If[compactRouteQ,
    routeSpecName = StringReplace[specName, "_index_spec" -> "_route_spec"];
    Print["private theorem ", routeSpecName, " :"];
    If[allExact,
      Print["    forall i : Fin ", len, ", values", targetN, "RouteNat (",
        indexName, " i).1 = ", routeCtor, " i := by"],
      exceptionalCase = First[exceptionalCases];
      Print["    forall i : Fin ", len, ", Not (i = (", exceptionalCase,
        " : Fin ", len, ")) ->"];
      Print["      values", targetN, "RouteNat (", indexName,
        " i).1 = ", routeCtor, " i := by"]
    ];
    Print["  native_decide"];
    Print[""];
    Print["theorem ", specName, " (i : Fin ", len, ") :"];
    Print["    values", targetN, " (", indexName, " i) = ", body, " := by"];
    If[allExact,
      Print["  change (values", targetN, "RouteNat (", indexName,
        " i).1).eval = ", body];
      Print["  rw [", routeSpecName, " i]"];
      Print["  rfl"],
      Print["  by_cases h : i = (", exceptionalCase, " : Fin ", len, ")"];
      Print["  \[CenterDot] subst i"];
      lines = rangeCaseEqualityProof[targetN, codeFn[exceptionalCase]];
      Scan[Print["    " <> #] &, lines];
      Print["  \[CenterDot] change (values", targetN, "RouteNat (", indexName,
        " i).1).eval = ", body];
      Print["    rw [", routeSpecName, " i h]"];
      Print["    rfl"]
    ],
    Print["set_option linter.unreachableTactic false in"];
    Print["set_option linter.unnecessarySeqFocus false in"];
    Print["set_option linter.unusedTactic false in"];
    Print["set_option maxHeartbeats ", If[targetN >= 15, 20000000, 4000000], " in"];
    Print["theorem ", specName, " (i : Fin ", len, ") :"];
    Print["    values", targetN, " (", indexName, " i) = ", body, " := by"];
    Print["  fin_cases i"];
    Do[
      code = codeFn[i - 1];
      If[rangeCaseExactQ[targetN, code],
        Print["  next => rfl"],
        lines = rangeCaseEqualityProof[targetN, code];
        Print["  next =>"];
        Scan[Print["    " <> #] &, lines]
      ],
      {i, len}
    ]
  ];
  Print[""];
  Print["theorem ", name, " (i : Fin ", len, ") :"];
  Print["    (Set.range values", targetN, ") (", body, ") := by"];
  Print["  exact \:27e8", indexName, " i, ", specName, " i\:27e9"];
  Print[""]
];

printBinaryRangeLemmaFor[targetN_Integer, name_String, len1_Integer, len2_Integer, body_String, codeFn_] := Module[
  {code, idx, lines, indexNatName, indexName, specName, targetLen},
  targetLen = Length[values[targetN]];
  indexNatName = rangeIndexNatName[name];
  indexName = rangeIndexName[name];
  specName = rangeIndexSpecName[name];
  Print["def ", indexNatName, " : Nat -> Nat -> Nat"];
  Do[
    code = codeFn[i - 1, j - 1];
    idx = rangeIndex[targetN, code];
    If[! IntegerQ[idx],
      Print["  | ", i - 1, ", ", j - 1, " => 0 -- missing value index for ", codeString[code]],
      Print["  | ", i - 1, ", ", j - 1, " => ", idx]
    ],
    {i, len1}, {j, len2}
  ];
  Print["  | _, _ => 0"];
  Print[""];
  Print["def ", indexName, " (i : Fin ", len1, ") (j : Fin ", len2, ") : Fin ", targetLen, " :="];
  Print["  Fin.ofNat ", targetLen, " (", indexNatName, " i.1 j.1)"];
  Print[""];
  Print["set_option linter.unreachableTactic false in"];
  Print["set_option linter.unnecessarySeqFocus false in"];
  Print["set_option linter.unusedTactic false in"];
  Print["set_option maxHeartbeats ", If[targetN >= 15, 20000000, 4000000], " in"];
  Print["theorem ", specName, " (i : Fin ", len1, ") (j : Fin ", len2, ") :"];
  Print["    values", targetN, " (", indexName, " i j) = ", body, " := by"];
  Print["  fin_cases i <;> fin_cases j"];
  Do[
    code = codeFn[i - 1, j - 1];
    If[rangeCaseExactQ[targetN, code],
      Print["  next => rfl"],
      lines = rangeCaseEqualityProof[targetN, code];
      Print["  next =>"];
      Scan[Print["    " <> #] &, lines]
    ],
    {i, len1}, {j, len2}
  ];
  Print[""];
  Print["theorem ", name, " (i : Fin ", len1, ") (j : Fin ", len2, ") :"];
  Print["    (Set.range values", targetN, ") (", body, ") := by"];
  Print["  exact \:27e8", indexName, " i j, ", specName, " i j\:27e9"];
  Print[""]
];

printLeanRange[n_Integer] := Module[{},
  If[n =!= 12 && n =!= 13 && n =!= 14 && n =!= 15,
    Print["lean-range is currently implemented only for n = 12, n = 13, n = 14, or n = 15"];
    Exit[2]
  ];
  If[n === 15,
    printUnaryRangeLemmaFor[
      15,
      "sqrt_values14_mem_range_values15",
      455,
      "Real.sqrt (values14 i)",
      Function[i, {"sqrt", 14, i}]
    ];
    printUnaryRangeLemmaFor[
      15,
      "one_add_values13_mem_range_values15",
      264,
      "1 + values13 i",
      Function[i, {"add", 1, 0, 13, i}]
    ];
    (* Lower one-add and two-add cases are proved in Lean from padding
       monotonicity instead of emitted as generated range tables. *)
    printUnaryRangeLemmaFor[
      15,
      "sqrt_two_add_values10_mem_range_values15",
      54,
      "Real.sqrt 2 + values10 i",
      Function[i, {"add", 4, 1, 10, i}]
    ];
    printBinaryRangeLemmaFor[
      15,
      "values5_add_values9_mem_range_values15",
      5,
      33,
      "values5 i + values9 j",
      Function[{i, j}, {"add", 5, i, 9, j}]
    ];
    printBinaryRangeLemmaFor[
      15,
      "values6_add_values8_mem_range_values15",
      8,
      20,
      "values6 i + values8 j",
      Function[{i, j}, {"add", 6, i, 8, j}]
    ];
    printBinaryRangeLemmaFor[
      15,
      "values7_add_values7_mem_range_values15",
      13,
      13,
      "values7 i + values7 j",
      Function[{i, j}, {"add", 7, i, 7, j}]
    ];
    Return[]
  ];
  If[n === 14,
    printUnaryRangeLemmaFor[
      14,
      "sqrt_values13_mem_range_values14",
      264,
      "Real.sqrt (values13 i)",
      Function[i, {"sqrt", 13, i}]
    ];
    printUnaryRangeLemmaFor[
      14,
      "one_add_values12_mem_range_values14",
      154,
      "1 + values12 i",
      Function[i, {"add", 1, 0, 12, i}]
    ];
    printUnaryRangeLemmaFor[
      14,
      "sqrt_two_add_values9_mem_range_values14",
      33,
      "Real.sqrt 2 + values9 i",
      Function[i, {"add", 4, 1, 9, i}]
    ];
    printBinaryRangeLemmaFor[
      14,
      "values5_add_values8_mem_range_values14",
      5,
      20,
      "values5 i + values8 j",
      Function[{i, j}, {"add", 5, i, 8, j}]
    ];
    printBinaryRangeLemmaFor[
      14,
      "values6_add_values7_mem_range_values14",
      8,
      13,
      "values6 i + values7 j",
      Function[{i, j}, {"add", 6, i, 7, j}]
    ];
    Return[]
  ];
  If[n === 13,
    printUnaryRangeLemmaFor[
      13,
      "sqrt_values12_mem_range_values13",
      154,
      "Real.sqrt (values12 i)",
      Function[i, {"sqrt", 12, i}]
    ];
    printUnaryRangeLemmaFor[
      13,
      "one_add_values11_mem_range_values13",
      91,
      "1 + values11 i",
      Function[i, {"add", 1, 0, 11, i}]
    ];
    printUnaryRangeLemmaFor[
      13,
      "one_add_values10_mem_range_values13",
      54,
      "1 + values10 i",
      Function[i, {"add", 1, 0, 10, i}]
    ];
    printUnaryRangeLemmaFor[
      13,
      "one_add_values9_mem_range_values13",
      33,
      "1 + values9 i",
      Function[i, {"add", 1, 0, 9, i}]
    ];
    printUnaryRangeLemmaFor[
      13,
      "two_add_values9_mem_range_values13",
      33,
      "2 + values9 i",
      Function[i, {"add", 3, 1, 9, i}]
    ];
    printUnaryRangeLemmaFor[
      13,
      "one_add_values8_mem_range_values13",
      20,
      "1 + values8 i",
      Function[i, {"add", 1, 0, 8, i}]
    ];
    printUnaryRangeLemmaFor[
      13,
      "sqrt_two_add_values8_mem_range_values13",
      20,
      "Real.sqrt 2 + values8 i",
      Function[i, {"add", 4, 1, 8, i}]
    ];
    printUnaryRangeLemmaFor[
      13,
      "two_add_values8_mem_range_values13",
      20,
      "2 + values8 i",
      Function[i, {"add", 3, 1, 8, i}]
    ];
    printBinaryRangeLemmaFor[
      13,
      "values5_add_values7_mem_range_values13",
      5,
      13,
      "values5 i + values7 j",
      Function[{i, j}, {"add", 5, i, 7, j}]
    ];
    printBinaryRangeLemmaFor[
      13,
      "values6_add_values6_mem_range_values13",
      8,
      8,
      "values6 i + values6 j",
      Function[{i, j}, {"add", 6, i, 6, j}]
    ];
    Return[]
  ];
  printUnaryRangeLemma[
    "sqrt_values11_mem_range_values12",
    "i",
    "Real.sqrt (values11 i)",
    91,
    Function[i, {"sqrt", 11, i}]
  ];
  printUnaryRangeLemma[
    "one_add_values10_mem_range_values12",
    "i",
    "1 + values10 i",
    54,
    Function[i, {"add", 1, 0, 10, i}]
  ];
  printUnaryRangeLemma[
    "one_add_values9_mem_range_values12",
    "i",
    "1 + values9 i",
    33,
    Function[i, {"add", 1, 0, 9, i}]
  ];
  printUnaryRangeLemma[
    "one_add_values8_mem_range_values12",
    "i",
    "1 + values8 i",
    20,
    Function[i, {"add", 1, 0, 8, i}]
  ];
  printUnaryRangeLemma[
    "two_add_values8_mem_range_values12",
    "i",
    "2 + values8 i",
    20,
    Function[i, {"add", 3, 1, 8, i}]
  ];
  printUnaryRangeLemma[
    "one_add_values7_mem_range_values12",
    "i",
    "1 + values7 i",
    13,
    Function[i, {"add", 1, 0, 7, i}]
  ];
  printUnaryRangeLemma[
    "sqrt_two_add_values7_mem_range_values12",
    "i",
    "Real.sqrt 2 + values7 i",
    13,
    Function[i, {"add", 4, 1, 7, i}]
  ];
  printUnaryRangeLemma[
    "two_add_values7_mem_range_values12",
    "i",
    "2 + values7 i",
    13,
    Function[i, {"add", 3, 1, 7, i}]
  ];
  printBinaryRangeLemma[
    "values5_add_values6_mem_range_values12",
    5,
    8,
    "values5 i + values6 j",
    Function[{i, j}, {"add", 5, i, 6, j}]
  ];
];

SetAttributes[writeGenerated, HoldRest];
writeGenerated[n_Integer, name_String, expr_] := Module[{path, stream},
  path = FileNameJoin[{
    "Oeis", "A158415", "computations", "wolfram", "generated",
    "a158415-n" <> ToString[n] <> "-" <> name <> ".txt"
  }];
  stream = OpenWrite[path, CharacterEncoding -> "UTF8", FormatType -> OutputForm, PageWidth -> Infinity];
  Block[{$Output = {stream}}, expr];
  Close[stream];
  Print[path]
];

printLeanBundle[n_Integer] := (
  writeGenerated[n, "summary", printSummary[]];
  writeGenerated[n, "lean-table", printLeanTable[n]];
  writeGenerated[n, "adjacent", printAdjacent[n]];
  writeGenerated[n, "special-lean", printLeanSpecial[n]];
  writeGenerated[n, "strict-lean", printLeanStrict[n]];
  writeGenerated[n, "range-lean", printLeanRange[n]];
  If[MemberQ[{14, 15}, n],
    writeGenerated[n, "interval-order-module-lean", printLeanIntervalOrderModule[n]]
  ];
  If[MemberQ[{14, 15}, n],
    writeGenerated[n, "membership-lean", printLeanMembership[n]]
  ]
);

Switch[mode,
  "summary", printSummary[],
  "numeric-summary", printSummary[],
  "table", printTable[target],
  "numeric-table", printTable[target],
  "collisions", printCollisions[target],
  "numeric-collisions", printCollisions[target],
  "routes", printRoutes[target],
  "numeric-routes", printRoutes[target],
  "lean-table", printLeanTable[target],
  "numeric-lean-table", printLeanTable[target],
  "adjacent", printAdjacent[target],
  "numeric-adjacent", printAdjacent[target],
  "lean-special", printLeanSpecial[target],
  "numeric-lean-special", printLeanSpecial[target],
  "lean-strict", printLeanStrict[target],
  "numeric-lean-strict", printLeanStrict[target],
  "lean-interval-order-module", printLeanIntervalOrderModule[target],
  "numeric-lean-interval-order-module", printLeanIntervalOrderModule[target],
  "lean-membership", printLeanMembership[target],
  "numeric-lean-membership", printLeanMembership[target],
  "lean-range", printLeanRange[target],
  "numeric-lean-range", printLeanRange[target],
  "lean-bundle", printLeanBundle[target],
  "numeric-lean-bundle", printLeanBundle[target],
  _, Print["unknown mode: ", mode]; Exit[2]
];

Exit[];
