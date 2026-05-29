import{p as q}from"./chunk-6ZKBGPIT-GL34UMSk.js";import{p as H}from"./wardley-L42UT6IY-YAZPMKU5-DDuTT_-d.js";import{g as J,s as Q,a as Y,b as ee,x as te,v as ae,c as s,l as w,d as ie,K as re,a9 as se,aa as oe,ab as L,ac as ne,f as le,C as ce,ad as de,L as pe}from"./Mermaid.vue_vue_type_script_setup_true_lang-6FAncDSV.js";import"./index-CRfOPVpS.js";import"./modules/vue-CnHgG7HT.js";import"./modules/shiki-Czlm1gp1.js";import"./modules/file-saver-B7oFTzqn.js";var ge=pe.pie,C={sections:new Map,showData:!1},u=C.sections,D=C.showData,he=structuredClone(ge),ue=s(()=>structuredClone(he),"getConfig"),fe=s(()=>{u=new Map,D=C.showData,ce()},"clear"),me=s(({label:e,value:a})=>{if(a<0)throw new Error(`"${e}" has invalid value: ${a}. Negative values are not allowed in pie charts. All slice values must be >= 0.`);u.has(e)||(u.set(e,a),w.debug(`added new section: ${e}, with value: ${a}`))},"addSection"),ve=s(()=>u,"getSections"),xe=s(e=>{D=e},"setShowData"),Se=s(()=>D,"getShowData"),M={getConfig:ue,clear:fe,setDiagramTitle:ae,getDiagramTitle:te,setAccTitle:ee,getAccTitle:Y,setAccDescription:Q,getAccDescription:J,addSection:me,getSections:ve,setShowData:xe,getShowData:Se},we=s((e,a)=>{q(e,a),a.setShowData(e.showData),e.sections.map(a.addSection)},"populateDb"),Ce={parse:s(async e=>{const a=await H("pie",e);w.debug(a),we(a,M)},"parse")},De=s(e=>`
  .pieCircle{
    stroke: ${e.pieStrokeColor};
    stroke-width : ${e.pieStrokeWidth};
    opacity : ${e.pieOpacity};
  }
  .pieOuterCircle{
    stroke: ${e.pieOuterStrokeColor};
    stroke-width: ${e.pieOuterStrokeWidth};
    fill: none;
  }
  .pieTitleText {
    text-anchor: middle;
    font-size: ${e.pieTitleTextSize};
    fill: ${e.pieTitleTextColor};
    font-family: ${e.fontFamily};
  }
  .slice {
    font-family: ${e.fontFamily};
    fill: ${e.pieSectionTextColor};
    font-size:${e.pieSectionTextSize};
    // fill: white;
  }
  .legend text {
    fill: ${e.pieLegendTextColor};
    font-family: ${e.fontFamily};
    font-size: ${e.pieLegendTextSize};
  }
`,"getStyles"),$e=De,ye=s(e=>{const a=[...e.values()].reduce((r,n)=>r+n,0),$=[...e.entries()].map(([r,n])=>({label:r,value:n})).filter(r=>r.value/a*100>=1);return de().value(r=>r.value).sort(null)($)},"createPieArcs"),Te=s((e,a,$,y)=>{w.debug(`rendering pie chart
`+e);const r=y.db,n=ie(),T=re(r.getConfig(),n.pie),A=40,o=18,p=4,c=450,d=c,f=se(a),l=f.append("g");l.attr("transform","translate("+d/2+","+c/2+")");const{themeVariables:i}=n;let[b]=oe(i.pieOuterStrokeWidth);b??=2;const _=T.textPosition,g=Math.min(d,c)/2-A,G=L().innerRadius(0).outerRadius(g),B=L().innerRadius(g*_).outerRadius(g*_);l.append("circle").attr("cx",0).attr("cy",0).attr("r",g+b/2).attr("class","pieOuterCircle");const h=r.getSections(),O=ye(h),P=[i.pie1,i.pie2,i.pie3,i.pie4,i.pie5,i.pie6,i.pie7,i.pie8,i.pie9,i.pie10,i.pie11,i.pie12];let m=0;h.forEach(t=>{m+=t});const E=O.filter(t=>(t.data.value/m*100).toFixed(0)!=="0"),v=ne(P).domain([...h.keys()]);l.selectAll("mySlices").data(E).enter().append("path").attr("d",G).attr("fill",t=>v(t.data.label)).attr("class","pieCircle"),l.selectAll("mySlices").data(E).enter().append("text").text(t=>(t.data.value/m*100).toFixed(0)+"%").attr("transform",t=>"translate("+B.centroid(t)+")").style("text-anchor","middle").attr("class","slice");const I=l.append("text").text(r.getDiagramTitle()).attr("x",0).attr("y",-400/2).attr("class","pieTitleText"),k=[...h.entries()].map(([t,S])=>({label:t,value:S})),x=l.selectAll(".legend").data(k).enter().append("g").attr("class","legend").attr("transform",(t,S)=>{const F=o+p,X=F*k.length/2,Z=12*o,j=S*F-X;return"translate("+Z+","+j+")"});x.append("rect").attr("width",o).attr("height",o).style("fill",t=>v(t.label)).style("stroke",t=>v(t.label)),x.append("text").attr("x",o+p).attr("y",o-p).text(t=>r.getShowData()?`${t.label} [${t.value}]`:t.label);const N=Math.max(...x.selectAll("text").nodes().map(t=>t?.getBoundingClientRect().width??0)),U=d+A+o+p+N,R=I.node()?.getBoundingClientRect().width??0,K=d/2-R/2,V=d/2+R/2,W=Math.min(0,K),z=Math.max(U,V)-W;f.attr("viewBox",`${W} 0 ${z} ${c}`),le(f,c,z,T.useMaxWidth)},"draw"),Ae={draw:Te},Le={parser:Ce,db:M,renderer:Ae,styles:$e};export{Le as diagram};
