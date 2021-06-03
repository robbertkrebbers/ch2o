# Copyright (c) 2012-2015, Robbert Krebbers.
# This file is distributed under the terms of the BSD license.
import os, glob, string

modules = ["prelude", "separation", "types", "memory", "refinements",
  "memory_refinements", "memory_separation", "core_c", "abstract_c",
  "axiomatic", "extraction"]
Rs = '-R . ch2o'
env = DefaultEnvironment(ENV = os.environ,tools=['default', 'Coq'], COQFLAGS=Rs)

# Coq dependencies
vs = [x for m in modules for x in glob.glob(m + '/*.v')]
if os.system('coqdep ' + Rs + ' ' + ' '.join(map(str, vs)) + ' > deps'): Exit(2)
ParseDepends('deps')

# coq2html
env.Command('./utils/coq2html.ml', 'utils/coq2html.mll',
  'ocamllex -q $SOURCE -o $TARGET')
t = env.Command('utils/coq2html', 'utils/coq2html.ml',
  'ocamlopt -o $TARGET str.cmxa $SOURCE')
env.Clean(t, 'utils/coq2html.o')
env.Clean(t, 'utils/coq2html.cmi')
env.Clean(t, 'utils/coq2html.cmx')

# Coq files
for v in vs:
  env.Coq(v)
  h = 'doc/ch2o.' + os.path.splitext(v)[0].replace('/','.') + '.html'
  glo = os.path.splitext(v)[0] + '.glob'
  env.Command(h, ['utils/coq2html',v,glo],'utils/coq2html -o '+h+' '+v)

# Parser
include = env.Command('parser/Include.ml', '',
  'echo let include_dir = ref \\"' + os.getcwd() + '/include\\" > $TARGET')
main = env.Command(['ch2o','ch2o.byte'], '',
  'ocamlbuild -j 2 -libs nums,str,unix\
   -I parser parser/Main.native parser/Main.byte &&\
   mv Main.native ch2o && mv Main.byte ch2o.byte')
AlwaysBuild(main)
env.Clean('extraction/extraction.vo', 'parser/Extracted.ml')
env.Clean('extraction/extraction.vo', 'parser/Extracted.mli')
env.Depends(main, include)
env.Depends(main, 'extraction/extraction.vo')
env.Clean(main, '_build')

# Coqidescript
env.CoqIdeScript('coqidescript', [])
