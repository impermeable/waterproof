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
