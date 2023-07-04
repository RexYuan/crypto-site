
# Setting up

1. [Install Hugo](https://gohugo.io/installation/)
2. `git submodule update --init --recursive`
3. `hugo server --navigateToChanged`
4. Preview at `http://localhost:1313/`

# Writing

1. `hugo new docs/file.md`
2. Edit `content/docs/file.md`

## Katex

Put the following at the top of the document to enable Katex:

```markdown
{{< katex />}}
{{< cl_macro >}}
```

Use `$math_inline$` and `$$math_block$$` as usual. Alternatively,
use `\\(math_inline\\)` and `\\[math_block\\]`.

See [Supported Functions](https://katex.org/docs/supported.html).

Note that line breaks must be escaped. For example:

```markdown
$$
\begin{array}{cc}
   a & b \\\\
   c & d
\end{array}
$$
```
