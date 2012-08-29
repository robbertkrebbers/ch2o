# -*- coding: utf-8 -*-
import SCons.Defaults, SCons.Tool, SCons.Util, os

def add_glob(target, source, env):
  base, _ = os.path.splitext(str(target[0]))
  target.append(base + ".glob")
  return target, source

Coq = SCons.Builder.Builder(
  action = '$COQCMD',
  suffix = '.vo',
  src_suffix = '.v',
  emitter = add_glob)

def make_coqidescript(target, source, env):
  open('coqidescript', 'w').write('#!/bin/sh\n' +
    env['COQIDE'] + ' ' + env['COQFLAGS'] + ' $@ \n')
  os.chmod('coqidescript', 0755)
  return 0

CoqIdeScript = SCons.Builder.Builder(
  action = make_coqidescript)

def generate(env):
  env['COQC'] = 'coqc'
  env['COQIDE'] = 'coqide'
  env['COQCMD'] = '$COQC $COQFLAGS -q $SOURCE'
  env.Append(BUILDERS = {
    'Coq': Coq,
    'CoqIdeScript' : CoqIdeScript
  })

def exists(env):
  return env.Detect('coqc')
