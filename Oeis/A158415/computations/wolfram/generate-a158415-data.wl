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
*)

ClearAll[
  codeString,
  leanValueExpr,
  leanCodeExpr,
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

printLeanTable[n_Integer] := Module[{name},
  name = "values" <> ToString[n] <> "Nat";
  Print["noncomputable def ", name, " : Nat -> Real"];
  Do[
    Print["  | ", i - 1, " => ", leanCodeExpr[values[n][[i, 2]]]],
    {i, Length[values[n]]}
  ];
  Print["  | _ => 0"];
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

printLeanStrict[n_Integer] := Module[{a, b, i1, i2, sqrtN, sqrtLen, addN, addLen},
  sqrtN = n - 1;
  sqrtLen = Length[values[sqrtN]];
  addN = n - 2;
  addLen = Length[values[addN]];
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
        Print["  next => exact sqrt_values", sqrtN, "_strictMono (by decide)"],
      MatchQ[a, {"add", 1, 0, addN, _Integer}] &&
          MatchQ[b, {"add", 1, 0, addN, _Integer}],
        i1 = a[[5]];
        i2 = b[[5]];
        Print[
          "  next =>"
        ];
        Print[
          "    change 1 + values" <> ToString[addN] <> " (" <> ToString[i1] <>
          " : Fin " <> ToString[addLen] <> ") < 1 + values" <> ToString[addN] <>
          " (" <> ToString[i2] <> " : Fin " <> ToString[addLen] <> ")"
        ];
        Print[
          "    linarith [values" <> ToString[addN] <>
          "_strictMono (by native_decide : (" <> ToString[i1] <> " : Fin " <>
          ToString[addLen] <> ") < " <> ToString[i2] <> ")]"
        ],
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
  Print["    ", body, " ∈ Set.range values12 := by"];
  Print["  fin_cases i"];
  Do[
    code = codeFn[i - 1];
    idx = valueIndex[12, exprValue[code]];
    If[! IntegerQ[idx],
      Print["  · fail \"missing value index for ", codeString[code], "\""],
      If[idx === 86 && code =!= values[12][[idx + 1, 2]],
        Print["  · exact ⟨(", idx, " : Fin 154), by a158415_twelve_table; rw [sqrt_four]⟩"],
        Print["  · exact ⟨(", idx, " : Fin 154), by a158415_twelve_table⟩"]
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
  Print["    ", body, " ∈ Set.range values12 := by"];
  Print["  fin_cases i <;> fin_cases j"];
  Do[
    code = codeFn[i - 1, j - 1];
    idx = valueIndex[12, exprValue[code]];
    If[! IntegerQ[idx],
      Print["  · fail \"missing value index for ", codeString[code], "\""],
      If[idx === 86 && code =!= values[12][[idx + 1, 2]],
        Print["  · exact ⟨(", idx, " : Fin 154), by a158415_twelve_table; rw [sqrt_four]⟩"],
        Print["  · exact ⟨(", idx, " : Fin 154), by a158415_twelve_table⟩"]
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

rangeCaseProof[targetN_Integer, code_] := Module[{idx, repCode, rep, body, rewrites},
  idx = valueIndex[targetN, exprValue[code]];
  If[! IntegerQ[idx],
    {"fail \"missing value index for " <> codeString[code] <> "\""},
    repCode = values[targetN][[idx + 1, 2]];
    rep = leanCodeExpr[repCode];
    body = leanCodeExpr[code];
    If[rep === body,
      {
        "exact Exists.intro (" <> ToString[idx] <> " : Fin " <> ToString[Length[values[targetN]]] <> ") (by",
        "  change " <> rep <> " = " <> body,
        "  rfl",
        ")"
      },
      rewrites = DeleteDuplicates[Join[highValueRefs[repCode], highValueRefs[code]]];
      {
        "exact Exists.intro (" <> ToString[idx] <> " : Fin " <> ToString[Length[values[targetN]]] <> ") (by",
        "  change " <> rep <> " = " <> body,
        Sequence @@ (("  " <> highValueRewrite[#]) & /@ rewrites),
        "  a158415_twelve_table <;> try rw [sqrt_four] <;> norm_num",
        ")"
      }
    ]
  ]
];

printUnaryRangeLemmaFor[targetN_Integer, name_String, len_Integer, body_String, codeFn_] := Module[
  {code, lines},
  Print["set_option linter.unreachableTactic false in"];
  Print["set_option linter.unnecessarySeqFocus false in"];
  Print["set_option linter.unusedTactic false in"];
  Print["set_option maxHeartbeats ", If[targetN >= 15, 20000000, 4000000], " in"];
  Print["theorem ", name, " (i : Fin ", len, ") :"];
  Print["    (Set.range values", targetN, ") (", body, ") := by"];
  Print["  fin_cases i"];
  Do[
    code = codeFn[i - 1];
    lines = rangeCaseProof[targetN, code];
    Print["  next =>"];
    Scan[Print["    " <> #] &, lines],
    {i, len}
  ];
  Print[""]
];

printBinaryRangeLemmaFor[targetN_Integer, name_String, len1_Integer, len2_Integer, body_String, codeFn_] := Module[
  {code, lines},
  Print["set_option linter.unreachableTactic false in"];
  Print["set_option linter.unnecessarySeqFocus false in"];
  Print["set_option linter.unusedTactic false in"];
  Print["set_option maxHeartbeats ", If[targetN >= 15, 20000000, 4000000], " in"];
  Print["theorem ", name, " (i : Fin ", len1, ") (j : Fin ", len2, ") :"];
  Print["    (Set.range values", targetN, ") (", body, ") := by"];
  Print["  fin_cases i <;> fin_cases j"];
  Do[
    code = codeFn[i - 1, j - 1];
    lines = rangeCaseProof[targetN, code];
    Print["  next =>"];
    Scan[Print["    " <> #] &, lines],
    {i, len1}, {j, len2}
  ];
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
      "one_add_values11_mem_range_values14",
      91,
      "1 + values11 i",
      Function[i, {"add", 1, 0, 11, i}]
    ];
    printUnaryRangeLemmaFor[
      14,
      "one_add_values10_mem_range_values14",
      54,
      "1 + values10 i",
      Function[i, {"add", 1, 0, 10, i}]
    ];
    printUnaryRangeLemmaFor[
      14,
      "two_add_values10_mem_range_values14",
      54,
      "2 + values10 i",
      Function[i, {"add", 3, 1, 10, i}]
    ];
    printUnaryRangeLemmaFor[
      14,
      "one_add_values9_mem_range_values14",
      33,
      "1 + values9 i",
      Function[i, {"add", 1, 0, 9, i}]
    ];
    printUnaryRangeLemmaFor[
      14,
      "sqrt_two_add_values9_mem_range_values14",
      33,
      "Real.sqrt 2 + values9 i",
      Function[i, {"add", 4, 1, 9, i}]
    ];
    printUnaryRangeLemmaFor[
      14,
      "two_add_values9_mem_range_values14",
      33,
      "2 + values9 i",
      Function[i, {"add", 3, 1, 9, i}]
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
  writeGenerated[n, "range-lean", printLeanRange[n]]
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
  "lean-range", printLeanRange[target],
  "numeric-lean-range", printLeanRange[target],
  "lean-bundle", printLeanBundle[target],
  "numeric-lean-bundle", printLeanBundle[target],
  _, Print["unknown mode: ", mode]; Exit[2]
];

Exit[];
