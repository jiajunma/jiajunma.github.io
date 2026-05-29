import{_ as i}from"./slidev/CodeBlockWrapper.vue_vue_type_script_setup_true_lang-D5P2vNPT.js";import{o as p,b as c,w as o,g as s,d as u,m as d,D as n,v as m,x as f,z as a}from"./modules/vue-CnHgG7HT.js";import{I as _}from"./slidev/default-DLcbewft.js";import{u as g,f as k}from"./slidev/context-BZxAtxhE.js";import"./modules/unplugin-icons-BlPU76cY.js";import"./index-CRfOPVpS.js";import"./modules/shiki-Czlm1gp1.js";const v={class:"two-col"},h={class:"code-compact"},T={__name:"session05B.md__slidev_8",setup(w){const{$clicksContext:l,$frontmatter:r}=g();return l.setup(),(y,e)=>{const t=i;return p(),c(_,m(f(a(k)(a(r),7))),{default:o(()=>[e[2]||(e[2]=s("h1",null,"The Repair Loop",-1)),s("div",v,[s("div",null,[s("div",h,[u(t,d({},{title:"",ranges:[]}),{default:o(()=>[...e[0]||(e[0]=[s("pre",{class:"shiki shiki-themes vitesse-dark vitesse-light slidev-code",style:{"--shiki-dark":"#dbd7caee","--shiki-light":"#393a34","--shiki-dark-bg":"#121212","--shiki-light-bg":"#ffffff"}},[s("code",{class:"language-text"},[s("span",{class:"line"},[s("span",null,"solution = generate_then_self_improve(problem)")]),n(`
`),s("span",{class:"line"},[s("span",null,"verify, good = verify_solution(problem, solution)")]),n(`
`),s("span",{class:"line"},[s("span",null,"correct_count, error_count = 1, 0")]),n(`
`),s("span",{class:"line"},[s("span")]),n(`
`),s("span",{class:"line"},[s("span",null,"for i in range(30):")]),n(`
`),s("span",{class:"line"},[s("span",null,'    if good != "yes":')]),n(`
`),s("span",{class:"line"},[s("span",null,"        solution = regenerate_with_bug_report(...)")]),n(`
`),s("span",{class:"line"},[s("span",null,"        correct_count = 0; error_count += 1")]),n(`
`),s("span",{class:"line"},[s("span",null,"    verify, good = verify_solution(problem, solution)")]),n(`
`),s("span",{class:"line"},[s("span",null,'    if good == "yes":')]),n(`
`),s("span",{class:"line"},[s("span",null,"        correct_count += 1; error_count = 0")]),n(`
`),s("span",{class:"line"},[s("span",null,"    if correct_count >= 5:  return solution   # ACCEPT")]),n(`
`),s("span",{class:"line"},[s("span",null,"    if error_count   >= 10: return None        # GIVE UP")])])],-1)])]),_:1},16)])]),e[1]||(e[1]=s("div",null,[s("pre",{class:"prompt"},[n("Below is the "),s("span",{class:"kw"},"bug report"),n(". "),s("span",{class:"kw"},"If you agree"),n(` with an
item, improve your solution so it is complete and
rigorous. Note that the evaluator `),s("span",{class:"kw"},`can
misunderstand`),n(` your solution and make mistakes.
`),s("span",{class:"kw"},"If you do not agree"),n(", "),s("span",{class:"kw"},`add detailed
explanations`),n(` to avoid such misunderstanding.
`)]),s("div",{class:"box"},[n(" The repair prompt allows for a "),s("strong",null,"wrong verifier"),n(": agree and fix, or disagree and clarify. ")])],-1))])]),_:1},16)}}};export{T as default};
