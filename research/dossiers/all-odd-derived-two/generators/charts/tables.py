from pathlib import Path

for kind in ('Pair', 'Jet'):
    prefix = 'RibbonOdd' + kind
    body = Path(prefix + 'Cert.lean').read_text()
    stop = body.index('private theorem check' + ('j' if kind == 'Jet' else '') + '0')
    Path(prefix + 'Table.lean').write_text(body[:stop] + 'end RibbonOddFinite\n')
