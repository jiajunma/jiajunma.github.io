import{_ as c}from"./slidev/CodeBlockWrapper.vue_vue_type_script_setup_true_lang-D5P2vNPT.js";import{o as r,b as p,w as a,g as n,d,m as u,D as s,v as m,x as f,z as l}from"./modules/vue-CnHgG7HT.js";import{I as _}from"./slidev/default-DLcbewft.js";import{u as h,f as g}from"./slidev/context-BZxAtxhE.js";import"./modules/unplugin-icons-BlPU76cY.js";import"./index-CRfOPVpS.js";import"./modules/shiki-Czlm1gp1.js";const v={class:"two-col-wide"},k={class:"code-compact"},V={__name:"session05B.md__slidev_21",setup(x){const{$clicksContext:t,$frontmatter:i}=h();return t.setup(),(b,e)=>{const o=c;return r(),p(_,m(f(l(g)(l(i),20))),{default:a(()=>[e[2]||(e[2]=n("h1",null,"The Verdict Contract: verification.json",-1)),n("div",v,[n("div",null,[n("div",k,[d(o,u({},{title:"",ranges:[]}),{default:a(()=>[...e[0]||(e[0]=[n("pre",{class:"shiki shiki-themes vitesse-dark vitesse-light slidev-code",style:{"--shiki-dark":"#dbd7caee","--shiki-light":"#393a34","--shiki-dark-bg":"#121212","--shiki-light-bg":"#ffffff"}},[n("code",{class:"language-text"},[n("span",{class:"line"},[n("span",null,"{")]),s(`
`),n("span",{class:"line"},[n("span",null,' "verification_hash": "<echoed from prompt>",')]),s(`
`),n("span",{class:"line"},[n("span",null,' "verdict": "accepted | gap | critical",')]),s(`
`),n("span",{class:"line"},[n("span",null,' "verification_report": {')]),s(`
`),n("span",{class:"line"},[n("span",null,'   "summary": "…",')]),s(`
`),n("span",{class:"line"},[n("span",null,'   "checked_items": [')]),s(`
`),n("span",{class:"line"},[n("span",null,"     { location, status:accepted|gap|critical, notes }")]),s(`
`),n("span",{class:"line"},[n("span",null,"   ],")]),s(`
`),n("span",{class:"line"},[n("span",null,'   "gaps":            [ { location, issue } ],')]),s(`
`),n("span",{class:"line"},[n("span",null,'   "critical_errors": [ { location, issue } ],')]),s(`
`),n("span",{class:"line"},[n("span",null,'   "external_reference_checks": [')]),s(`
`),n("span",{class:"line"},[n("span",null,"     { location, reference, status, notes }")]),s(`
`),n("span",{class:"line"},[n("span",null,"   ]")]),s(`
`),n("span",{class:"line"},[n("span",null,"   # status ∈ verified_in_nodes | missing_from_nodes")]),s(`
`),n("span",{class:"line"},[n("span",null,"   #   | verified_external_theorem_node")]),s(`
`),n("span",{class:"line"},[n("span",null,"   #   | insufficient_information | not_applicable")]),s(`
`),n("span",{class:"line"},[n("span",null," },")]),s(`
`),n("span",{class:"line"},[n("span",null,' "repair_hint": ""')]),s(`
`),n("span",{class:"line"},[n("span",null,"}")])])],-1)])]),_:1},16)])]),e[1]||(e[1]=n("div",null,[n("div",{class:"box-green"},[n("strong",null,"Three-valued, not yes/no."),s(),n("code",null,"gap"),s(" = conclusion may hold, justification thin; "),n("code",null,"critical"),s(" = statement or strategy may be wrong. When unsure: "),n("code",null,"gap"),s(", never "),n("code",null,"accepted"),s(".")]),n("div",{class:"box"},[n("strong",null,"Coupling is schema-enforced."),s(" A JSON Schema (draft 2020-12, "),n("code",null,"if/then"),s(") ties verdict→contents: "),n("code",null,"accepted"),s(" ⇒ gaps & critical_errors empty, "),n("code",null,'repair_hint ""'),s('. You cannot "accept" while listing a gap.')]),n("div",{class:"box-orange"},[n("code",null,"verification_hash"),s(" echoes unchanged → binds the verdict to the "),n("strong",null,"exact text checked"),s(", so a stale verdict can't be applied to a changed proof.")])],-1))])]),_:1},16)}}};export{V as default};
