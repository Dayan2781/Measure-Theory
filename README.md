# Хэмжээний онол

МУИС-ийн «Хэмжээний онол» хичээлийн ном (16 лекц, 16 семинар), [PreTeXt](https://pretextbook.org) форматаар.

## Бүтэц

- `source/main.ptx`: номын үндсэн файл
- `source/chNN-*.ptx`: долоо хоног бүрийн бүлэг (лекц + семинарын бодлого)
- `source/appX-*.ptx`: хавсралтууд
- `source/docinfo.ptx`: математик макрос, монгол гарчгууд
- `publication/publication.ptx`: хэвлэлийн тохиргоо (бодолт нуух гэх мэт)

## Бүтээх

```bash
pip install -r requirements.txt
pretext build web     # HTML: output/web
pretext build print   # PDF (xelatex, CMU Serif фонт хэрэгтэй)
```

`main` салбарт push хийх бүрт GitHub Actions номыг бүтээж GitHub Pages дээр нийтэлнэ.
