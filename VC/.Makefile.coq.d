sumarray.vo sumarray.glob sumarray.v.beautified sumarray.required_vo: sumarray.v 
sumarray.vos sumarray.vok sumarray.required_vos: sumarray.v 
reverse.vo reverse.glob reverse.v.beautified reverse.required_vo: reverse.v 
reverse.vos reverse.vok reverse.required_vos: reverse.v 
append.vo append.glob append.v.beautified append.required_vo: append.v 
append.vos append.vok append.required_vos: append.v 
stack.vo stack.glob stack.v.beautified stack.required_vo: stack.v 
stack.vos stack.vok stack.required_vos: stack.v 
strlib.vo strlib.glob strlib.v.beautified strlib.required_vo: strlib.v 
strlib.vos strlib.vok strlib.required_vos: strlib.v 
hash.vo hash.glob hash.v.beautified hash.required_vo: hash.v 
hash.vos hash.vok hash.required_vos: hash.v 
hints.vo hints.glob hints.v.beautified hints.required_vo: hints.v 
hints.vos hints.vok hints.required_vos: hints.v 
stdlib.vo stdlib.glob stdlib.v.beautified stdlib.required_vo: stdlib.v 
stdlib.vos stdlib.vok stdlib.required_vos: stdlib.v 
stdlib2.vo stdlib2.glob stdlib2.v.beautified stdlib2.required_vo: stdlib2.v 
stdlib2.vos stdlib2.vok stdlib2.required_vos: stdlib2.v 
stack2.vo stack2.glob stack2.v.beautified stack2.required_vo: stack2.v 
stack2.vos stack2.vok stack2.required_vos: stack2.v 
triang2.vo triang2.glob triang2.v.beautified triang2.required_vo: triang2.v 
triang2.vos triang2.vok triang2.required_vos: triang2.v 
main2.vo main2.glob main2.v.beautified main2.required_vo: main2.v 
main2.vos main2.vok main2.required_vos: main2.v 
Preface.vo Preface.glob Preface.v.beautified Preface.required_vo: Preface.v stack.vo
Preface.vos Preface.vok Preface.required_vos: Preface.v stack.vos
Verif_sumarray.vo Verif_sumarray.glob Verif_sumarray.v.beautified Verif_sumarray.required_vo: Verif_sumarray.v Preface.vo sumarray.vo
Verif_sumarray.vos Verif_sumarray.vok Verif_sumarray.required_vos: Verif_sumarray.v Preface.vos sumarray.vos
Verif_reverse.vo Verif_reverse.glob Verif_reverse.v.beautified Verif_reverse.required_vo: Verif_reverse.v Preface.vo reverse.vo
Verif_reverse.vos Verif_reverse.vok Verif_reverse.required_vos: Verif_reverse.v Preface.vos reverse.vos
Verif_stack.vo Verif_stack.glob Verif_stack.v.beautified Verif_stack.required_vo: Verif_stack.v Preface.vo stack.vo hints.vo
Verif_stack.vos Verif_stack.vok Verif_stack.required_vos: Verif_stack.v Preface.vos stack.vos hints.vos
Verif_triang.vo Verif_triang.glob Verif_triang.v.beautified Verif_triang.required_vo: Verif_triang.v Preface.vo stack.vo
Verif_triang.vos Verif_triang.vok Verif_triang.required_vos: Verif_triang.v Preface.vos stack.vos
Verif_append1.vo Verif_append1.glob Verif_append1.v.beautified Verif_append1.required_vo: Verif_append1.v Preface.vo append.vo
Verif_append1.vos Verif_append1.vok Verif_append1.required_vos: Verif_append1.v Preface.vos append.vos
Verif_append2.vo Verif_append2.glob Verif_append2.v.beautified Verif_append2.required_vo: Verif_append2.v Preface.vo append.vo Verif_append1.vo
Verif_append2.vos Verif_append2.vok Verif_append2.required_vos: Verif_append2.v Preface.vos append.vos Verif_append1.vos
Verif_strlib.vo Verif_strlib.glob Verif_strlib.v.beautified Verif_strlib.required_vo: Verif_strlib.v Preface.vo strlib.vo hints.vo
Verif_strlib.vos Verif_strlib.vok Verif_strlib.required_vos: Verif_strlib.v Preface.vos strlib.vos hints.vos
Hashfun.vo Hashfun.glob Hashfun.v.beautified Hashfun.required_vo: Hashfun.v 
Hashfun.vos Hashfun.vok Hashfun.required_vos: Hashfun.v 
Verif_hash.vo Verif_hash.glob Verif_hash.v.beautified Verif_hash.required_vo: Verif_hash.v Preface.vo hash.vo hints.vo Hashfun.vo
Verif_hash.vos Verif_hash.vok Verif_hash.required_vos: Verif_hash.v Preface.vos hash.vos hints.vos Hashfun.vos
VSU_intro.vo VSU_intro.glob VSU_intro.v.beautified VSU_intro.required_vo: VSU_intro.v 
VSU_intro.vos VSU_intro.vok VSU_intro.required_vos: VSU_intro.v 
Spec_stack.vo Spec_stack.glob Spec_stack.v.beautified Spec_stack.required_vo: Spec_stack.v stack2.vo Spec_stdlib.vo
Spec_stack.vos Spec_stack.vok Spec_stack.required_vos: Spec_stack.v stack2.vos Spec_stdlib.vos
Spec_triang.vo Spec_triang.glob Spec_triang.v.beautified Spec_triang.required_vo: Spec_triang.v triang2.vo Spec_stdlib.vo Spec_stack.vo
Spec_triang.vos Spec_triang.vok Spec_triang.required_vos: Spec_triang.v triang2.vos Spec_stdlib.vos Spec_stack.vos
Spec_stdlib.vo Spec_stdlib.glob Spec_stdlib.v.beautified Spec_stdlib.required_vo: Spec_stdlib.v Preface.vo stdlib.vo
Spec_stdlib.vos Spec_stdlib.vok Spec_stdlib.required_vos: Spec_stdlib.v Preface.vos stdlib.vos
VSU_stack.vo VSU_stack.glob VSU_stack.v.beautified VSU_stack.required_vo: VSU_stack.v Spec_stdlib.vo Spec_stack.vo stack2.vo
VSU_stack.vos VSU_stack.vok VSU_stack.required_vos: VSU_stack.v Spec_stdlib.vos Spec_stack.vos stack2.vos
VSU_triang.vo VSU_triang.glob VSU_triang.v.beautified VSU_triang.required_vo: VSU_triang.v Spec_stdlib.vo Spec_stack.vo Spec_triang.vo triang2.vo
VSU_triang.vos VSU_triang.vok VSU_triang.required_vos: VSU_triang.v Spec_stdlib.vos Spec_stack.vos Spec_triang.vos triang2.vos
VSU_stdlib.vo VSU_stdlib.glob VSU_stdlib.v.beautified VSU_stdlib.required_vo: VSU_stdlib.v stdlib.vo Spec_stdlib.vo
VSU_stdlib.vos VSU_stdlib.vok VSU_stdlib.required_vos: VSU_stdlib.v stdlib.vos Spec_stdlib.vos
VSU_main.vo VSU_main.glob VSU_main.v.beautified VSU_main.required_vo: VSU_main.v main2.vo stdlib.vo stack2.vo triang2.vo Spec_stdlib.vo Spec_stack.vo Spec_triang.vo VSU_stdlib.vo VSU_stack.vo VSU_triang.vo
VSU_main.vos VSU_main.vok VSU_main.required_vos: VSU_main.v main2.vos stdlib.vos stack2.vos triang2.vos Spec_stdlib.vos Spec_stack.vos Spec_triang.vos VSU_stdlib.vos VSU_stack.vos VSU_triang.vos
VSU_stdlib2.vo VSU_stdlib2.glob VSU_stdlib2.v.beautified VSU_stdlib2.required_vo: VSU_stdlib2.v stdlib2.vo Spec_stdlib.vo
VSU_stdlib2.vos VSU_stdlib2.vok VSU_stdlib2.required_vos: VSU_stdlib2.v stdlib2.vos Spec_stdlib.vos
VSU_main2.vo VSU_main2.glob VSU_main2.v.beautified VSU_main2.required_vo: VSU_main2.v main2.vo stdlib2.vo stack2.vo triang2.vo Spec_stdlib.vo Spec_stack.vo Spec_triang.vo VSU_stdlib2.vo VSU_stack.vo VSU_triang.vo
VSU_main2.vos VSU_main2.vok VSU_main2.required_vos: VSU_main2.v main2.vos stdlib2.vos stack2.vos triang2.vos Spec_stdlib.vos Spec_stack.vos Spec_triang.vos VSU_stdlib2.vos VSU_stack.vos VSU_triang.vos
Postscript.vo Postscript.glob Postscript.v.beautified Postscript.required_vo: Postscript.v 
Postscript.vos Postscript.vok Postscript.required_vos: Postscript.v 
Bib.vo Bib.glob Bib.v.beautified Bib.required_vo: Bib.v 
Bib.vos Bib.vok Bib.required_vos: Bib.v 
