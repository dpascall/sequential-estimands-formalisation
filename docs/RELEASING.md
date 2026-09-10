# Publish this early release

Suggested repository name: `sequential-learning`. Suggested tag:
`v0.1.0-alpha.1`. The proposed release title and body are in `RELEASE_NOTES.md`.

## Upload

Create an empty GitHub repository. From the unpacked directory containing
`README.md` and `lakefile.toml`, run these commands, replacing
`YOUR_REPOSITORY_URL` with that repository's URL:

```bash
git init -b main
git add .
git update-index --chmod=+x scripts/*.sh
git commit -m "Prepare v0.1.0-alpha.1 research snapshot"
git remote add origin YOUR_REPOSITORY_URL
git push -u origin main
```

Upload the directory contents, including the GitHub workflow and Git
configuration files, rather than making the ZIP the repository's only file.

## Final metadata

Add the actual repository URL as `repository-code` in `CITATION.cff` and adjust
`date-released` if publication occurs after the snapshot date. Commit and push
those changes before tagging. No project license was supplied; add your chosen
license if you intend to license the code for reuse.

Author metadata comes from the supplied manuscript. No repository URL, DOI, or
ORCID has been invented. The citation file follows the
[Citation File Format](https://github.com/citation-file-format/citation-file-format).

## Pre-release

Check the **Lean verification** workflow in GitHub Actions. After it succeeds,
create a release from the checked commit using tag `v0.1.0-alpha.1`, paste the
contents of `RELEASE_NOTES.md`, and mark it as a **pre-release**. Compiler
verification and manuscript correspondence are separate parts of its status.
See [GitHub's release instructions](https://docs.github.com/en/repositories/releasing-projects-on-github/managing-releases-in-a-repository)
for the release form.

Cite the release page or exact tagged commit so the application identifies
this version. GitHub supplies source archives for the tag; a GitHub release
does not itself provide a DOI.

## Application reference

Append the published release URL to:

> Pascall, D. J. (2026). *SequentialLearning: Lean formalisation of sequential
> estimands* (v0.1.0-alpha.1) [Computer software; early research release]. GitHub.

Possible accompanying wording, once published:

> An early Lean formalisation of the sequential-estimand framework is
> available, covering its geometric taxonomy and core learning results;
> development and manuscript–formalisation correspondence are ongoing.

Use `docs/STATUS.md` for this snapshot's qualifications. It should not be
described as complete verification of the manuscript.
