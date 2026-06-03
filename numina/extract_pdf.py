import fitz
import sys
import os

pdf_path = '/data/clones/2540825244/m2r-group-7/16-made-easy/numina/blueprints/16-made-easy/source/16-made-easy-source.pdf'
pdf = fitz.open(pdf_path)
out_path = sys.argv[1] if len(sys.argv) > 1 else '/data/clones/2540825244/m2r-group-7/16-made-easy/numina/extracted.txt'
with open(out_path, 'w') as f:
    for i, p in enumerate(pdf):
        f.write(f'\n========= PAGE {i+1} =========\n')
        f.write(p.get_text())
print('wrote', out_path)
