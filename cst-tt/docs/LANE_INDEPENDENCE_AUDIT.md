# Lane independence audit

The aggregate is exact conjunction, not score aggregation. The complete Boolean table has eight rows and exactly one positive row. Six component-splice controls realize every one-lane and two-lane combination of S-R, S-L, and A while the aggregate remains false. These are logical independence controls, not claims that every splice is a physically coherent migration episode.

| Control | S-R | S-L | A | Aggregate |
|---|---|---|---|---|
| FIACH-C01 | true | false | false | false |
| FIACH-C02 | false | true | false | false |
| FIACH-C03 | false | false | true | false |
| FIACH-C04 | true | true | false | false |
| FIACH-C05 | true | false | true | false |
| FIACH-C06 | false | true | true | false |
