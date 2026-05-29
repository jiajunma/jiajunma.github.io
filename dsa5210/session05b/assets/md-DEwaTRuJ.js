import{o as n,b as i,w as l,g as e,ad as s,v as c,x as p,T as a}from"./modules/vue-Z1bZjFKP.js";import{I as u}from"./slidev/default-Bw4f9V0N.js";import{u as d,f as m}from"./slidev/context-B8YUwS_H.js";import"./index-C7UMSAds.js";import"./modules/shiki-D8NRPJIT.js";const y={__name:"session05B.md__slidev_6",setup(f){const{$clicksContext:o,$frontmatter:r}=d();return o.setup(),(h,t)=>(n(),i(u,c(p(a(m)(a(r),5))),{default:l(()=>[...t[0]||(t[0]=[e("h1",null,"IMO25’s Verification Prompt",-1),e("pre",{class:"prompt"},[s("You are an expert mathematician and a "),e("span",{class:"kw"},"meticulous grader"),s(` for an
IMO-level exam. ... A solution is judged correct only if `),e("span",{class:"kw"},`every
step is rigorously justified`),s(`.

Your sole task is to find and report all issues in the provided
solution. You must act as a `),e("span",{class:"kw"},"verifier, NOT a solver"),s(". "),e("span",{class:"kw"},`Do NOT
attempt to correct`),s(` the errors or fill the gaps you find.
`)],-1),e("div",{class:"two-col"},[e("div",null,[e("pre",{class:"prompt"},[s("a. "),e("span",{class:"kw"},"Critical Error"),s(`:
   any error that `),e("span",{class:"kw"},`breaks the
   logical chain`),s(` of the proof.
   Fallacies (e.g. "A>B, C>D" implies
   "A-C>B-D") and factual errors
   (e.g. "2+3=6").
   Procedure: explain it; do NOT check
   steps that rely on it; still scan
   independent parts (other cases).
`)])]),e("div",null,[e("pre",{class:"prompt"},[s("b. "),e("span",{class:"kw"},"Justification Gap"),s(`:
   the conclusion may be right, but the
   argument is `),e("span",{class:"kw"},`incomplete,
   hand-wavy`),s(`, or lacks rigor.
   Procedure: explain the gap; ASSUME the
   step's conclusion; then verify all
   subsequent steps.
`)])])],-1),e("div",{class:"box"},[s(" The verifier grades only the extracted "),e("strong",null,"Detailed Solution"),s('. Every issue is one of these two kinds — the taxonomy makes the verdict actionable, not a vague "looks wrong." ')],-1),e("div",{class:"source-note"},[s("Verbatim from "),e("code",null,"verification_system_prompt"),s(".")],-1)])]),_:1},16))}};export{y as default};
