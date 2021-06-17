/* eslint-disable no-unused-vars */
/* eslint-disable max-len */

export const empty = '(CoqAST ()';

export const emptyAst = `
(CoqAst (()
(loc ((
    (fname ToplevelInput)
    (line_nb 1)
    (bol_pos 0)
    (line_nb_last 2)
    (bol_pos_last 39)
    (bp 0)
    (ep 48)))
)))`;


export const sexp1 = `
(CoqAst ((v(
        (control())(attrs())(expr(
            VernacStartTheoremProof Theorem(((((v(Id p_implies_p)
        )
        (loc((
            (fname ToplevelInput)
            (line_nb 1)
            (bol_pos 0)
            (line_nb_last 1)
            (bol_pos_last 0)
            (bp 8)
            (ep 19))
        )))
        ())
        (()((v(CProdN((CLocalAssum(((v(Name(Id P)))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 29)(ep 30))))))(Default Explicit)((v(CSort(UNamed((CProp 0)))))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 33)(ep 37)))))))((v(CNotation()(InConstrEntry"_ -> _")((((v(CRef((v(Ser_Qualid(DirPath())(Id P)))(loc(((fname ToplevelInput)(line_nb 2)(bol_pos 39)(line_nb_last 2)(bol_pos_last 39)(bp 41)(ep 42)))))()))(loc(((fname ToplevelInput)(line_nb 2)(bol_pos 39)(line_nb_last 2)(bol_pos_last 39)(bp 41)(ep 42)))))((v(CRef((v(Ser_Qualid(DirPath())(Id P)))(loc(((fname ToplevelInput)(line_nb 2)(bol_pos 39)(line_nb_last 2)(bol_pos_last 39)(bp 46)(ep 47)))))()))(loc(((fname ToplevelInput)(line_nb 2)(bol_pos 39)(line_nb_last 2)(bol_pos_last 39)(bp 46)(ep 47))))))()()())))(loc(((fname ToplevelInput)(line_nb 2)(bol_pos 39)(line_nb_last 2)(bol_pos_last 39)(bp 41)(ep 47)))))))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 2)(bol_pos_last 39)(bp 22)(ep 47))))))))))))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 2)(bol_pos_last 39)(bp 0)(ep 48))))))
`;

export const sexpRequire = `(CoqAst((v((control())(attrs())(expr(VernacRequire()(false)(((v(Ser_Qualid(DirPath())(Id Reals)))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 15)(ep 20))))))))))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 21))))))`;

export const sexpHint = `(CoqAst((v((control())(attrs())(expr(VernacHints()(HintsResolve((((hint_priority())(hint_pattern()))true(HintsReference((v(Ser_Qualid(DirPath())(Id Rnot_lt_ge)))(loc(((fname ToplevelInput)(line_nb 10)(bol_pos 235)(line_nb_last 10)(bol_pos_last 235)(bp 248)(ep 258)))))))))))))(loc(((fname ToplevelInput)(line_nb 10)(bol_pos 235)(line_nb_last 10)(bol_pos_last 235)(bp 235)(ep 259))))))`;


export const Ltac2NB = `(CoqAst((v((control())(attrs())(expr(VernacRequire(((v(Ser_Qualid(DirPath())(Id Ltac2)))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 5)(ep 10))))))(false)(((v(Ser_Qualid(DirPath())(Id Ltac2)))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 26)(ep 31))))))))))(loc(((fname ToplevelInput)(line_nb 1)(bol_pos 0)(line_nb_last 1)(bol_pos_last 0)(bp 0)(ep 32))))))
(CoqAst((v((control())(attrs())(expr(VernacAddLoadPath(implicit false)(physical_path /home/doc/SEP/waterproof/coq_tactics/new_wplib/)(logical_path(DirPath((Id wplib))))))))(loc(((fname ToplevelInput)(line_nb 3)(bol_pos 148)(line_nb_last 3)(bol_pos_last 148)(bp 148)(ep 220))))))
(CoqAst((v((control())(attrs())(expr(VernacLoad false basic_contradiction))))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 221)(ep 246))))))
(CoqAst((v((control())(attrs())(expr(VernacStartTheoremProof Lemma(((((v(Id id))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 253)(ep 255)))))())(()((v(CProdN((CLocalAssum(((v(Name(Id n)))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 264)(ep 265))))))(Default Explicit)((v(CRef((v(Ser_Qualid(DirPath())(Id nat)))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 268)(ep 271)))))()))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 268)(ep 271)))))))((v(CNotation()(InConstrEntry"_ = _")((((v(CRef((v(Ser_Qualid(DirPath())(Id n)))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 273)(ep 274)))))()))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 273)(ep 274)))))((v(CRef((v(Ser_Qualid(DirPath())(Id n)))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 277)(ep 278)))))()))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 277)(ep 278))))))()()())))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 273)(ep 278)))))))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 257)(ep 278))))))))))))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 247)(ep 279))))))
(CoqAst((v((control())(attrs())(expr(VernacProof()()))))(loc(((fname ToplevelInput)(line_nb 4)(bol_pos 221)(line_nb_last 4)(bol_pos_last 221)(bp 280)(ep 286))))))
(CoqAst((v((control())(attrs())(expr(VernacExtend(VernacLtac2 0)((GenArg raw(ExtraArg ltac2_expr)"[raw: (ExtraArg ltac2_expr): ABSTRACT]")(GenArg raw(ExtraArg ltac_use_default)false))))))(loc(((fname ToplevelInput)(line_nb 5)(bol_pos 287)(line_nb_last 5)(bol_pos_last 287)(bp 291)(ep 317))))))
(CoqAst((v((control())(attrs())(expr(VernacAbort()))))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 318)(ep 324))))))
(CoqAst((v((control())(attrs())(expr(VernacStartTheoremProof Lemma(((((v(Id n_is_n))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 331)(ep 337)))))())(()((v(CProdN((CLocalAssum(((v(Name(Id n)))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 346)(ep 347))))))(Default Explicit)((v(CRef((v(Ser_Qualid(DirPath())(Id nat)))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 350)(ep 353)))))()))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 350)(ep 353)))))))((v(CNotation()(InConstrEntry"_ = _")((((v(CRef((v(Ser_Qualid(DirPath())(Id n)))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 355)(ep 356)))))()))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 355)(ep 356)))))((v(CRef((v(Ser_Qualid(DirPath())(Id n)))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 359)(ep 360)))))()))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 359)(ep 360))))))()()())))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 355)(ep 360)))))))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 339)(ep 360))))))))))))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 325)(ep 361))))))
(CoqAst((v((control())(attrs())(expr(VernacProof()()))))(loc(((fname ToplevelInput)(line_nb 6)(bol_pos 318)(line_nb_last 6)(bol_pos_last 318)(bp 362)(ep 368))))))
(CoqAst((v((control())(attrs())(expr(VernacExtend(VernacLtac2 0)((GenArg raw(ExtraArg ltac2_expr)"[raw: (ExtraArg ltac2_expr): ABSTRACT]")(GenArg raw(ExtraArg ltac_use_default)false))))))(loc(((fname ToplevelInput)(line_nb 7)(bol_pos 369)(line_nb_last 7)(bol_pos_last 369)(bp 373)(ep 381))))))
(CoqAst((v((control())(attrs())(expr(VernacExtend(VernacLtac2 0)((GenArg raw(ExtraArg ltac2_expr)"[raw: (ExtraArg ltac2_expr): ABSTRACT]")(GenArg raw(ExtraArg ltac_use_default)false))))))(loc(((fname ToplevelInput)(line_nb 8)(bol_pos 382)(line_nb_last 8)(bol_pos_last 382)(bp 386)(ep 412))))))
(CoqAst((v((control())(attrs())(expr(VernacExtend(VernacLtac2 0)((GenArg raw(ExtraArg ltac2_expr)"[raw: (ExtraArg ltac2_expr): ABSTRACT]")(GenArg raw(ExtraArg ltac_use_default)false))))))(loc(((fname ToplevelInput)(line_nb 9)(bol_pos 413)(line_nb_last 9)(bol_pos_last 413)(bp 417)(ep 431))))))
(CoqAst((v((control())(attrs())(expr(VernacEndProof(Proved Opaque())))))(loc(((fname ToplevelInput)(line_nb 10)(bol_pos 432)(line_nb_last 10)(bol_pos_last 432)(bp 432)(ep 436))))))`;
