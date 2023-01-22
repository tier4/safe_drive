# Documentation

You can contribute to documents you are reading now.
Documents are written in Markdown and located in [mdbook](https://github.com/tier4/safe_drive/tree/main/mdbook).
These Markdown files are compiled to HTML files and located in [docs](https://github.com/tier4/safe_drive/tree/main/docs),
and published at [https://tier4.github.io/safe_drive/](https://tier4.github.io/safe_drive/).

You can use (Mermaid)[https://mermaid.js.org/#/] notation in Markdown as follows.

```mermaid
graph TD;
    A-->B;
    A-->C;
    B-->D;
    C-->D;
```

The compilation can be done by `make` as follows.

```text
$ make doc
```

We are not native English speaker.
So, we need your help to improve documents!
