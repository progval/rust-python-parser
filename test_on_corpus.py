#!/usr/bin/env python3
import os
import sys
import ast
import difflib
import tempfile
import unittest
import astpretty
import subprocess

def test_file(path):
    with open(path) as f:
        expected_ast = astpretty.pformat(ast.parse(f.read()), show_position=False)
    printer_output = subprocess.check_output(['cargo', 'run', path])
    received_ast = astpretty.pformat(ast.parse(printer_output), show_position=False)
    if expected_ast == received_ast:
        print('{}: ok'.format(path))
        return
    print('========================')
    print(path)
    print('------------------------')
    #for line in difflib.unified_diff(received_ast, expected_ast): # OMG so slow
    #    print(line)
    with tempfile.NamedTemporaryFile('w+', prefix='expected-') as exp_file, \
            tempfile.NamedTemporaryFile('w+', prefix='received-') as received_file:
        exp_file.write(expected_ast)
        exp_file.seek(0)
        received_file.write(received_ast)
        received_file.seek(0)
        try:
            subprocess.check_output(
                    ['diff', '-u', received_file.name, exp_file.name],
                    universal_newlines=True)
        except subprocess.CalledProcessError as e:
            print(e.output)
        else:
            assert False, 'diff did not detect a different, but should have.'
    print('========================')

def test_dir(path):
    for (dirpath, dirname, filenames) in os.walk(path):
        if any(x.startswith('.') for x in dirpath.split(os.path.sep)):
            # dotfile
            continue
        for filename in filenames:
            if os.path.splitext(filename)[1] == '.py':
                test_file(os.path.join(dirpath, filename))



def main():
    for path in sys.argv[1:]:
        if os.path.isfile(path):
            test_file(path)
        elif os.path.isdir(path):
            test_dir(path)
        else:
            print('Error: no such file or directory: {}'.format(path))
            exit(1)

if __name__ == '__main__':
    main()
