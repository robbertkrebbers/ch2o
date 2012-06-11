import os, glob, string

nodes = ['./']
dirs = []
vs = []

env = DefaultEnvironment(ENV = os.environ, tools=['default', 'Coq'])

while nodes:
  node = nodes.pop()
  if node.endswith('.v') and not node.endswith('_old.v'):
    vs += [File(node)]
  if os.path.isdir(node):
    dirs += [node]
    nodes += glob.glob(node + '/*')

includes = ' '.join(map(lambda x: '-I ' + x, dirs[1:]))
Rs = '-R . CH2O'
coqcmd = 'coqc ${str(SOURCE)[:-2]} ' + Rs

env['COQFLAGS'] = Rs

for node in vs: env.Coq(node, COQCMD=coqcmd)

os.system('coqdep ' + ' '.join(map(str, vs)) + ' ' + includes + ' ' + Rs + ' > deps')
ParseDepends('deps')

open('coqidescript', 'w').write('#!/bin/sh\ncoqide ' + Rs + ' $@ \n')
os.chmod('coqidescript', 0755)

