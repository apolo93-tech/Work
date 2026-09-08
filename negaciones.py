#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Negaciones de existencia y que hizo el vendedor despues.

  python negaciones.py --mes 2026-08
  python negaciones.py --mes 2026-08 --cartera Santay --muestra 25
  python negaciones.py --mes 2026-08 --excel

LO QUE SE EVALUA NO ES DECIR QUE NO
  Que falte una pieza es normal. Lo que separa a un vendedor de otro es que
  hace despues: ofrecer un sustituto, comprometer un aviso, o cortar seco.

LAS TRES REGLAS DEL GLOSARIO MAESTRO v3.0 QUE CAMBIAN EL METODO

  Regla 9 -- EL COMPROMISO PUEDE VENIR EN OTRO MENSAJE. Wilber dice "agotado"
    372 veces y en NINGUNA agrega la salida en el mismo mensaje, pero usa
    "pendientes por surtir" 30.1 veces por cada 1,000 -- doce veces mas que
    cualquier otra cartera. La manda aparte. Por eso la ventana de busqueda
    abarca los mensajes SIGUIENTES del vendedor al mismo contacto, no solo
    el mensaje de la negacion.

  Regla 10 -- CADA CARTERA NIEGA EN SU DIALECTO. Stef dice "agotado" 2.2
    veces por cada 1,000 mensajes y Jose V 70.8. Comparar conteos crudos
    mide vocabulario, no desabastecimiento. Por eso el score es el
    PORCENTAJE de negaciones que quedaron secas, que no depende de cuanto
    se niegue ni con que palabra.

  Regla 5 -- FOTO TRAS NEGAR = ALTERNATIVA. Un adjunto dentro de la ventana
    es oferta de sustituto, no negacion seca.

  Regla 11 -- "ahora veo" = "ahora verifico". Es proactividad, nunca
    negacion: el vendedor esta yendo a revisar.

QUE NO ES UNA NEGACION
  "no hay problema", "no hay de que", "no se preocupe" son cortesia.
  "dipsonible" es "disponible" mal escrito, o sea lo contrario.
  Se excluyen explicitamente; sin eso el conteo se infla con amabilidad.
"""
import os, re, sys, sqlite3, argparse, unicodedata, random
from collections import Counter, defaultdict

AQUI = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, AQUI)
import ingesta as ing
import tiempos as T
import solicitudes as SOL
import alternos as ALT

DB = ing.DB
REPORTES = os.path.join(os.path.dirname(AQUI), "reportes")

# La ventana ancha (15 min / 6 mensajes) capturaba fotos y frases de OTRA
# consulta posterior y las contaba como alternativa de esta negacion.
# Ajustada: la foto sigue la regla 5 del Maestro (5 min) y el texto se limita
# a los 3 mensajes siguientes, que es lo que dura una misma respuesta.
VENTANA_MIN = 10      # minutos maximos para el texto
VENTANA_MSGS = 3      # mensajes del vendedor que siguen siendo la misma respuesta
VENTANA_FOTO = 5      # minutos para el adjunto (regla 5 del Glosario Maestro)

# --- que cuenta como negacion de existencia -------------------------------
NEGACIONES = [
    ("sin fecha de ingreso", r"sin fecha de ingreso|no (?:hay|tenemos|tiene) fecha de ingreso"),
    ("no manejamos",         r"no (?:lo |la |los |las )?manej\w+|no trabajamos"),
    ("agotado",              r"\bagotad\w+|se (?:nos |me |le )?agot\w+|ya no (?:hay|tenemos)"),
    ("no tenemos",           r"no (?:lo |la |los |las )?ten\w+(?! fecha)|no (?:lo |la )?hay\b"),
    ("sin existencia",       r"sin existencia\w*|sin stock|fuera de stock"),
    ("de momento no",        r"de momento no|por el momento no|por ahora no|ahorita no"),
    ("no ingresa",           r"no (?:ha |han )?ingresad\w+|aun no ingres\w+|no (?:ha|han) llegado"),
    # "no viene" lo pide el glosario de disparadores del Gold Standard. En los
    # datos casi siempre habla de CONTENIDO y no de existencia: "no viene
    # completa", "no viene con base", "la boleta no viene completa". Solo
    # cuenta cuando NO lo sigue un complemento de contenido. De 23 apariciones
    # en agosto, unas 6 son negaciones de stock de verdad.
    ("no viene",             r"no vien[ea]n?\b"
                             r"(?!\s*(?:con\b|complet|suelt|en |la |el |los |las |incluid))"),
    ("no le ofrezco",        r"no (?:se |le )?(?:lo |la )?ofre\w+"),
    ("le quedo mal",         r"le qued[eo] mal"),
]
NEG_RX = [(k, re.compile(v)) for k, v in NEGACIONES]

# Cortesia que contiene "no hay" / "no tenemos" y NO es negacion de stock.
NO_ES_NEGACION = re.compile(
    r"no hay (?:problema|de que|cuidado|falla|prisa|apuro)|"
    r"no se preocupe|no hay porque|no tenga pena|no hay ningun problema")

# Falsos positivos de "no manejamos" que en realidad son piezas/motos que
# no se manejan en catalogo. Deben excluirse del score de los vendedores
# pero contabilizarse como oportunidad perdida.
OPP_CATALOGO_RX = re.compile(
    r"no manejamos[^.;]*?(?:moto|modelo|marca|medida|repuest|codigo|color|asi)|"
    r"para[^.;]*?(?:moto|modelo|marca|medida|repuest|codigo|color|asi)[^.;]*?no manejamos|"
    r"(?:moto|modelo|marca|medida|repuest|codigo|color|asi)[^.;]*?no manejamos"
)

# --- que cuenta como salida despues de negar ------------------------------
# OJO: estas frases tambien viven DENTRO de las negaciones -- "no tenemos el
# negro" contiene "tenemos el", y "de momento no le ofrezco" contiene "le
# ofrezco". Buscarlas a secas clasificaba 2,517 negaciones como si fueran su
# propia alternativa. Por eso cada coincidencia pasa por `sin_negador()`.
ALTERNATIVA = re.compile(
    r"le ofrezco|le puedo ofrecer|le ofrecemos|se la ofrezco|se lo ofrezco|"
    r"tenemos el|tenemos la|tengo el|tengo la|pero tenemos|le sirve|"
    r"le funciona|le queda|alterno|alternativo|equivalente|sustitut\w+|"
    r"similar|en cambio|otra marca|otra opcion|otra medida|tambien hay|"
    r"hay de|manejamos el|manejamos la|seria en|seria el|unicamente el|"
    r"unicamente la|solo en|si en|pero en marca|en marca")

# Palabras que, delante de una frase de alternativa, la dan vuelta.
# La coma cierra la clausula: en "no le ofrezco, seria en GTS" el negador
# aplica a lo primero, no a la alternativa que viene despues.
NEGADOR = re.compile(r"\b(?:no|sin|tampoco|nada)\b[^.;,]{0,14}$")


def sin_negador(texto, m):
    """True si la coincidencia NO viene negada por lo que la precede."""
    return not NEGADOR.search(texto[max(0, m.start() - 20):m.start()])


def busca_alternativa(texto):
    """Primera frase de alternativa que no este negada."""
    for m in ALTERNATIVA.finditer(texto):
        if sin_negador(texto, m):
            return m.group(0)
    return None
# Dar una FECHA de ingreso es comprometerse, aunque no se prometa avisar:
# "Agotado, ingresa el proximo mes" no es una negacion seca. Salio al revisar
# a mano una muestra de las clasificadas como secas.
#
# El Gold Standard cuenta como salidas validas cuatro cosas: equivalencia,
# FECHA de ingreso, APARTADO y derivacion.
#
# La primera version buscaba la fecha en su forma de manual ("ingresa el
# jueves") y encontro UN mensaje en todo agosto -- de ahi la conclusion, falsa,
# de que la gente no da fechas. Las da, pero VAGAS y en otra construccion:
#
#     "agotado de momento ingresan a finales de septiembre"
#     "Agotada perdone entran para mediados de septiembre"
#     "posiblemente ingrese el proximo mes"
#     "le comento que ingresan como a mediados de septiembre"
#
# Tres cosas las dejaban fuera: el verbo en subjuntivo (`ingrese`, `entren`),
# los conectores libres ("como a", "posiblemente"), y que "finales"/"principios"
# no estaban en la lista. Por eso ahora es verbo de ingreso + hasta 30
# caracteres + expresion de fecha, en vez de una secuencia rigida.
FECHA = (r"proxim\w+|siguiente|otra semana|finales?|principios|fin de|mediados|"
         r"lunes|martes|miercoles|jueves|viernes|sabado|"
         r"enero|febrero|marzo|abril|mayo|junio|julio|agosto|septiembre|"
         r"setiembre|octubre|noviembre|diciembre|\d{1,2}\s*(?:de|/)")

# EL APARTADO SE DICE "RESERVAR". Buscar solo "apartar" hizo concluir que el
# apartado no existia en estas carteras y que eso era "material de capacitacion
# directo". Era falso: la palabra local es RESERVAR.
#
#   "se lo puedo reservar"      "le tengo 5 reservadas por si las quiere"
#   "ya se lo reservamos"       "me confirma para poder reservarselo"
#
# En agosto: 103 mensajes con "reserv*" contra 46 con "apart*" de verdad.
#
# Ojo con "apartar": NO vale "aparte", que en estas carteras casi siempre
# significa "ademas" o "por separado" ("en cajas aparte", "cobrarian aparte").
# Y le faltaba el \b inicial, con lo que "le comaparto el dato" (typo de
# "comparto", 5 casos en agosto) entraba como apartado.
#
# NO se agregan "guardar", "separar" ni "le dejo". Se muestrearon los tres:
# de 178 mensajes en agosto, UNO era un apartado real. "guardapolvo" es una
# pieza, "por separado" significa que se vende suelto y "le dejo el dato" es
# mandar informacion.
RESERVA_NEGADA = re.compile(r"\bno\b[^.;,]{0,20}\breserv")
SEGUIMIENTO = re.compile(
    r"pendiente|surtir|le aviso|le informo|le informamos|informaremos|"
    r"le confirmo|le escribo|apenas (?:llegue|ingrese)|"
    r"estare informando|le estare|se lo agrego|lo anoto|queda anotado|"
    r"\bapart(?:ar|arl[oa]s?|arsel[oa]s?|o|amos|a|ada|ado)s?\b|"
    r"\breserv(?:a|ar|arl|arsel|ada|ado|amos|aron|aremos|e|o)\w*|"
    # "cuando nos ingrese le comento" -- el compromiso sin fecha. Va en los dos
    # ordenes: tambien se dice "le comento cuando nos ingrese el tren". Se exige
    # el "cuando + verbo de ingreso" para no tragarse "le comento que no hay".
    r"cuando\s+(?:nos\s+)?(?:ingres\w+|llegue|llegen|entre|venga)"
    r"[^.;]{0,25}?(?:le\s+(?:aviso|comento|informo|digo|escribo|confirmo)|"
    r"le\s+indicar|le\s+estare)|"
    r"le\s+(?:aviso|comento|informo|digo|escribo|indico)[^.;]{0,15}?"
    r"cuando\s+(?:nos\s+)?(?:ingres\w+|llegue|llegen|entre|venga)|"
    r"(?:le indicaremos|le avisamos|le estaremos)\s+(?:cuando|apenas)|"
    # verbo de ingreso + fecha, con conectores libres en medio
    r"(?:ingres\w+|llega\w+|llegue\w*|entra\w*|entren)\s[^.;]{0,30}?(?:" + FECHA + r")|"
    r"en (?:una|dos|tres|\d+) (?:semana|dia|mes)\w*|"
    r"esta (?:por|en) (?:ingresar|llegar|camino)|viene en camino|"
    r"est(?:amos|a) (?:en espera|esperando) (?:de |el |la )?(?:ingres|llegad|que ingrese)|"
    r"esperamos (?:nuevos )?ingresos")

# DERIVACION en el sentido del manual: "dejeme confirmar con bodega y le
# confirmo hoy". Faltaba toda la forma con "dejeme" + infinitivo, que es como
# se dice aca; solo estaba la de primera persona ("verifico", "consulto").
BUSQUEDA = re.compile(
    r"verifico|ahora veo|deje veo|reviso|voy a (?:buscar|revisar|ver)|"
    r"consulto|pregunto|en bodega|otra sucursal|otra tienda|averigu\w+|"
    r"deje(?:me)?\s+(?:confirmar|verificar|consultar|revisar|checar|chequear|"
    r"preguntar|averiguar|ver\b)|"
    r"(?:lo|la|le)\s+(?:consulto|verifico|averiguo)|"
    r"(?:se|lo|la)\s+solicit[oa]\s+a\s+(?:bodega|fabrica|casa matriz)")

def busca_seguimiento(texto):
    """SEGUIMIENTO, descartando la reserva NEGADA ("no se puede reservar").

    Python no admite lookbehind de ancho variable, asi que el "no" delante de
    "reserv" se filtra aca en vez de dentro del patron. Solo se descarta si la
    reserva era lo unico que habia: si el mensaje ademas promete avisar, sigue
    siendo seguimiento.
    """
    m = SEGUIMIENTO.search(texto)
    if m and m.group(0).startswith("reserv") and RESERVA_NEGADA.search(texto):
        resto = SEGUIMIENTO.search(texto[m.end():])
        return resto if resto and not resto.group(0).startswith("reserv") else None
    return m


CLASES = ["alternativa", "seguimiento", "busqueda", "seca"]


def norm(s):
    return unicodedata.normalize("NFKD", str(s or "").lower()).encode(
        "ascii", "ignore").decode()


def nk_cod(s):
    return re.sub(r"[^A-Z0-9]", "", (s or "").upper())


CODIGOS = None


def esc(s):
    cod = sys.stdout.encoding or "utf-8"
    return str(s).encode(cod, "replace").decode(cod)


def tipo_negacion(txt):
    """Devuelve la etiqueta mas especifica, o None. El orden importa:
    'sin fecha de ingreso' contiene 'no tenemos fecha' y es peor."""
    t = norm(txt)
    if NO_ES_NEGACION.search(t):
        return None
    if OPP_CATALOGO_RX.search(t):
        return "oportunidad_perdida"
    for etiqueta, rx in NEG_RX:
        if rx.search(t):
            return etiqueta
    return None


def analizar_cartera(con, cartera, mes):
    filas = con.execute(
        """select contact_id, fecha, direccion, content_type, texto,
                  sender_nombre, sender_id
           from mensaje
           where cartera = ? and substr(fecha,1,7) = ?
           order by contact_id, fecha,
                    -- empate en el mismo segundo: el entrante va primero,
                    -- una respuesta no puede preceder a lo que responde
                    (direccion = 'outgoing')""", (cartera, mes)).fetchall()
    porc = defaultdict(list)
    for f in filas:
        porc[f[0]].append(f)

    casos = []
    for cid, lst in porc.items():
        for i, m in enumerate(lst):
            if m[2] != "outgoing" or m[3] != "text":
                continue
            vend = (m[5] or T.NOMBRE_POR_ID.get(m[6]) or "sin identificar")
            if m[6] in T.IDS_EXCLUIDOS:
                continue
            etiqueta = tipo_negacion(m[4])
            if not etiqueta:
                continue

            # que pidio el cliente: ultimo entrante antes de la negacion
            pedido = ""
            for k in range(i - 1, max(-1, i - 8), -1):
                if lst[k][2] == "incoming" and lst[k][4]:
                    pedido = lst[k][4]
                    break

            # la salida puede estar en el MISMO mensaje o en los siguientes
            # Ventana = TURNO del vendedor: todo lo que dice antes de que el
            # cliente vuelva a escribir es parte de la misma respuesta. Es mas
            # fiel que un numero fijo de mensajes y no se contamina con la
            # consulta siguiente. Probado: con ventana de 2 horas el 52% de
            # las secas "cambiaba", pero eran intercambios posteriores
            # distintos; acotado al turno, cambia el 3.9% y son reales.
            t0 = T.parse(m[1])
            posterior, adjunto = norm(m[4]), False
            resto = ""
            for k in range(i + 1, len(lst)):
                if lst[k][2] == "incoming":
                    break
                dt = (T.parse(lst[k][1]) - t0).total_seconds()
                if dt > VENTANA_MIN * 60:
                    break
                if lst[k][2] != "outgoing":
                    continue
                if lst[k][3] == "attachment":
                    # La foto se acepta estrictamente en los primeros 5 min (regla 5)
                    # desde la negación original.
                    if dt <= VENTANA_FOTO * 60:
                        adjunto = True
                    continue
                resto += " " + (lst[k][4] or "")
            posterior += " " + norm(resto)

            # Ofrecer OTRO codigo tambien es ofrecer una alternativa, aunque
            # no se use ninguna de las frases. Se valida contra el catalogo.
            otro_codigo = None
            for x in SOL.TOK.findall(resto):
                if SOL.es_codigo(x, CODIGOS) and nk_cod(x) not in nk_cod(m[4]):
                    otro_codigo = x
                    break

            # se guardan las frases que dispararon la clasificacion (pueden ser multiples)
            clases_detectadas = []
            evidencias = []

            mm_alt = busca_alternativa(posterior)
            if mm_alt:
                clases_detectadas.append("alternativa")
                evidencias.append(f"alt: {mm_alt}")
            elif otro_codigo:
                clases_detectadas.append("alternativa")
                evidencias.append(f"alt: (codigo {otro_codigo})")
            elif adjunto:
                clases_detectadas.append("alternativa")
                evidencias.append("alt: (foto)")

            mm_seg = busca_seguimiento(posterior)
            if mm_seg:
                clases_detectadas.append("seguimiento")
                evidencias.append(f"seg: {mm_seg.group(0)}")

            mm_busq = BUSQUEDA.search(posterior)
            if mm_busq:
                clases_detectadas.append("busqueda")
                evidencias.append(f"busq: {mm_busq.group(0)}")

            if not clases_detectadas:
                clase_principal = "seca"
                clases_str = "seca"
                ev = ""
            else:
                # la clase principal sigue la precedencia
                if "alternativa" in clases_detectadas:
                    clase_principal = "alternativa"
                elif "seguimiento" in clases_detectadas:
                    clase_principal = "seguimiento"
                else:
                    clase_principal = "busqueda"

                clases_str = ", ".join(clases_detectadas)
                ev = " | ".join(evidencias)

            # una seca que ademas cierra el hilo es la peor variante
            cierra = clase_principal == "seca" and (
                i == len(lst) - 1 or
                all(x[2] == "outgoing" for x in lst[i + 1:i + 3]) is False and
                not any(x[2] == "outgoing" for x in lst[i + 1:]))

            casos.append({
                "cartera": cartera, "contact_id": cid, "fecha": m[1],
                "vendedor": vend.strip(), "tipo": etiqueta, "clase": clase_principal,
                "clases_str": clases_str, "clases_detectadas": clases_detectadas,
                "cierra": cierra, "por_adjunto": adjunto, "evidencia": ev,
                "pedido": (pedido or "")[:120], "negacion": (m[4] or "")[:160],
                # lo que dijo DESPUES de negar, en crudo: es lo que hace falta
                # para mostrar el caso completo en los ejemplos del reporte
                "salida": " ".join(resto.split())[:200],
                "posterior": posterior # pasamos el texto posterior crudo normalizado para la proactividad
            })
    return casos


# --------------------------------------------------------------------------
# Cruce con inventario: habia algo que ofrecer?
# --------------------------------------------------------------------------
# Solo se puede desde el 21-ago: la carga diaria de existencias arranco ese
# dia, asi que del 1 al 20 no hay contra que validar. Es la restriccion que
# manda -- no el metodo.
DESDE_INVENTARIO = "2026-08-21"


def existencias_por_fecha(con, fechas):
    """{fecha: {codigo: existencia}} para no consultar la base por cada pieza."""
    out = {}
    for f in fechas:
        d = {}
        for cod, e in con.execute(
                """select codigo, existencia from existencia_hist
                   where valido_desde <= ? and
                         (valido_hasta is null or valido_hasta > ?)""", (f, f)):
            d[cod] = e
        out[f] = d
    return out


def resolver_pieza(con, caso, stock, prod, por_cabeza):
    """Que pedia el cliente, y habia eso o un alterno con existencia?

    Devuelve (veredicto, detalle). Si no se puede identificar la pieza el
    veredicto es 'no determinable' -- que es la respuesta honesta y, como se
    ve en los totales, la mas frecuente.
    """
    f = caso["fecha"][:10]
    disp = stock.get(f, {})

    # 1) el codigo citado por el vendedor es la vinculacion mas firme
    cods = [x for x in SOL.TOK.findall(caso["negacion"] or "")
            if SOL.es_codigo(x, CODIGOS)]
    origen = "codigo del vendedor"
    if not cods:
        pedidos = [x for x in SOL.TOK.findall(caso["pedido"] or "")
                   if SOL.es_codigo(x, CODIGOS)]
        # Si el cliente mando VARIOS codigos no se sabe cual nego el vendedor.
        # Caso real: "36jz0001 y 36JZ0027" -> "la culata no se la ofrezco".
        # El primero es un kit de valvulas con 1,432 unidades y la negacion
        # era de la culata: cruzarlos acusa a alguien por una pieza que no
        # nego. Con un solo codigo la vinculacion si es razonable.
        cods = pedidos if len(pedidos) == 1 else []
        origen = "codigo del cliente"
    for x in cods:
        cod = ALT.REAL.get(SOL.nk(x))
        if cod and cod in prod:
            e = disp.get(cod)
            if e is None:
                break
            if e > 0:
                return "NEGO teniendo existencia", f"{cod} tenia {e:.0f} ({origen})"
            alts = alternos_rapido(cod, disp, prod, por_cabeza)
            if alts:
                return "agotado, HABIA alterno", ", ".join(
                    f"{c}({v:.0f})" for c, v in alts[:4])
            return "agotado y sin alterno", cod

    # 2) sin codigo: nombre de la pieza + moto que menciono el cliente
    texto = (caso["pedido"] or "") + " " + (caso["negacion"] or "")
    cands = ALT.candidatos_por_texto_rapido(texto, disp, prod, por_cabeza)

    if not cands:
        return "oportunidad_perdida_catalogo", "no se maneja por el momento"

    con_stock = [(c, v) for c, v in cands if v > 0]
    if con_stock:
        return "HABIA algo con existencia", ", ".join(
            f"{c}({v:.0f})" for c, v in con_stock[:4])

    return "todo agotado (por nombre+modelo)", cands[0][0]


def alternos_rapido(cod, disp, prod, por_cabeza):
    a = prod[cod]
    out = []
    for otro in por_cabeza.get(a["cabeza"], []):
        if otro == cod or not ALT.es_alterno(a, prod[otro]):
            continue
        e = disp.get(otro, 0)
        if e and e > 0:
            out.append((otro, e))
    out.sort(key=lambda x: -x[1])
    return out


def calcular_resolucion(caso):
    clases = caso.get("clases_detectadas", [])
    evidencia = caso.get("evidencia", "")
    posterior = caso.get("posterior", "")

    if "alternativa" in clases:
        # Check si ofreción código compatible (menciona un código y es alternativo)
        if "codigo" in evidencia.lower() or re.search(r'\d+[a-zA-Z]+|[a-zA-Z]+\d+', posterior):
            return 50 # Alternativa + codigo compatible
        return 50 # Alternativa real

    if "seguimiento" in clases:
        if re.search(FECHA, posterior):
            return 40 # Fecha/compromiso concreto
        if re.search(r'le aviso|le informo|le confirmo|le escribo', posterior):
            return 30 # Seguimiento concreto
        return 20 # Solo seguimiento generico

    if "busqueda" in clases:
        if re.search(r'bodega|sucursal|tienda', posterior):
            return 35 # Búsqueda en bodega/sucursal
        return 15 # Búsqueda sin resultado

    return 0 # Negación seca


def calcular_proactividad(caso):
    posterior = caso.get("posterior", "")
    pts_detecta = 0
    pts_busca = 0
    pts_compromiso = 0
    pts_incertidumbre = 0
    pts_mantiene = 0

    # 1. Detecta que puede hacer algo más (max 3)
    if re.search(r'dejeme revisar|ahora veo|deje veo|voy a (?:revisar|ver)', posterior):
        pts_detecta = max(pts_detecta, 2)
        if re.search(r'bodega|sucursal|tienda|fabrica|casa matriz|alterno|codigo|sustituto', posterior):
            pts_detecta = 3
    elif "busqueda" in caso.get("clases_detectadas", []):
         pts_detecta = max(pts_detecta, 2)

    # 2. Busca activamente (max 5)
    if re.search(r'voy a|dejeme|reviso', posterior):
        pts_busca = max(pts_busca, 1)
    if re.search(r'bodega', posterior):
        pts_busca = max(pts_busca, 3)
    if re.search(r'sucursal|tienda', posterior):
        pts_busca = max(pts_busca, 3)
    if re.search(r'fabrica|casa matriz', posterior):
        pts_busca = max(pts_busca, 4)
    if len(re.findall(r'bodega|sucursal|tienda|fabrica|casa matriz', posterior)) >= 2:
        pts_busca = 5

    # 3. Compromete acción posterior (max 5)
    if re.search(r'voy a revisar', posterior):
        pts_compromiso = max(pts_compromiso, 1)
    if re.search(r'le aviso|le confirmo|le informo', posterior):
        pts_compromiso = max(pts_compromiso, 3)
    if re.search(r'apenas|cuando', posterior) and re.search(r'le escribo|le aviso|le confirmo', posterior):
        pts_compromiso = max(pts_compromiso, 4)
    if re.search(r'hoy|mañana|' + FECHA, posterior) and re.search(r'le aviso|le confirmo', posterior):
        pts_compromiso = 5

    # 4. Reduce incertidumbre (max 4)
    if re.search(r'le aviso', posterior):
        pts_incertidumbre = max(pts_incertidumbre, 2)
    if re.search(r'apenas ingrese|cuando llegue', posterior):
        pts_incertidumbre = max(pts_incertidumbre, 3)
    if re.search(FECHA, posterior):
        pts_incertidumbre = 4

    # 5. Mantiene venta viva (max 3)
    if re.search(r'espere|confirme', posterior):
        pts_mantiene = max(pts_mantiene, 1)
    if "seguimiento" in caso.get("clases_detectadas", []) or "alternativa" in caso.get("clases_detectadas", []):
        pts_mantiene = max(pts_mantiene, 2)
    if re.search(r'reserv|apart', posterior):
        pts_mantiene = 3

    total = pts_detecta + pts_busca + pts_compromiso + pts_incertidumbre + pts_mantiene
    return min(20, total)


def calcular_calidad_conversacional(caso):
    pts = 10
    clase = caso.get("clase")
    cierra = caso.get("cierra")

    if clase == "seca":
        if cierra:
            pts -= 15 # Negación seca + conversación terminada
        else:
            pts -= 8 # Negación seca sin cierre
    return pts


def calcular_gestion_oportunidad(caso):
    pts = 20
    veredicto = caso.get("veredicto")

    # La penalización se aplica independientemente de si la respuesta fue seca o no
    if veredicto == "NEGO teniendo existencia":
        pts -= 20
    elif veredicto == "agotado, HABIA alterno":
        pts -= 15
    elif veredicto == "HABIA algo con existencia":
        pts -= 10
    return pts

def score(cs, usar_inventario=False):
    """Calcula el Índice de Resolución ante Negaciones (IRN)."""
    if not cs:
        return 100.0

    # Excluir oportunidades perdidas del score del vendedor
    cs_validos = [c for c in cs if c["tipo"] != "oportunidad_perdida"]
    if not cs_validos:
        return 100.0

    total_score = 0

    for c in cs_validos:
        res = calcular_resolucion(c)
        proact = calcular_proactividad(c)
        conv = calcular_calidad_conversacional(c)
        gest = calcular_gestion_oportunidad(c) if usar_inventario and "veredicto" in c else 20

        c_score = res + proact + conv + gest
        total_score += c_score

    promedio = total_score / len(cs_validos)

    # Reincidencia (hasta -15)
    porcli = Counter(c["contact_id"] for c in cs_validos if c["clase"] == "seca")
    reinc_penalty = 0
    for cid, count in porcli.items():
        if count == 3: reinc_penalty = max(reinc_penalty, 3)
        elif count == 4: reinc_penalty = max(reinc_penalty, 6)
        elif count == 5: reinc_penalty = max(reinc_penalty, 10)
        elif count >= 6: reinc_penalty = max(reinc_penalty, 15)

    return max(0.0, min(100.0, promedio - reinc_penalty))

def calcular_nivel_confianza(n):
    if n < 15: return "MUY BAJA"
    if n < 30: return "BAJA"
    if n < 60: return "MEDIA"
    if n < 100: return "ALTA"
    return "MUY ALTA"

def pct(n, t):
    return 100.0 * n / t if t else 0.0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mes", required=True)
    ap.add_argument("--cartera")
    ap.add_argument("--muestra", type=int, default=0)
    ap.add_argument("--excel", action="store_true")
    ap.add_argument("--inventario", action="store_true",
                    help="cruza cada negacion contra la existencia de ese dia")
    a = ap.parse_args()

    global CODIGOS
    con = sqlite3.connect(DB)
    con.text_factory = lambda b: b.decode("utf-8", "replace")
    CODIGOS = SOL.cargar_codigos(con)
    carteras = ([a.cartera] if a.cartera else
                [r[0] for r in con.execute(
                    "select distinct cartera from mensaje order by 1")])

    cts_inv = dict(((r[0], r[1]), r[2]) for r in con.execute(
        "select cartera, contact_id, nombre from contacto"))
    todo = []
    por_cart = {}
    for cart in carteras:
        cs = analizar_cartera(con, cart, a.mes)
        por_cart[cart] = cs
        todo += cs

    print("\n" + "=" * 88)
    print(f"  NEGACIONES Y ALTERNATIVAS - {a.mes}")
    print("  ventana: el turno del vendedor -- hasta que el cliente vuelva a escribir")
    print("=" * 88)

    if a.inventario:
        print(f"\n  {'Cartera':<12}{'Negac.':>9}{'alternativa':>13}{'seguim.':>10}"
              f"{'busqueda':>11}{'SECAS':>9}{'OPP':>8}{'IRN':>8}")
        print("  " + "-" * 83)
    else:
        print(f"\n  {'Cartera':<12}{'Negac.':>9}{'alternativa':>13}{'seguim.':>10}"
              f"{'busqueda':>11}{'SECAS':>9}{'IRN':>8}")
        print("  " + "-" * 75)

    for cart in carteras:
        cs = por_cart[cart]
        if not cs:
            continue
        cc = Counter(c["clase"] for c in cs if c["tipo"] != "oportunidad_perdida")
        cs_validos = len([c for c in cs if c["tipo"] != "oportunidad_perdida"])
        opp = sum(1 for c in cs if c["tipo"] == "oportunidad_perdida")

        base_stats = (f"  {cart:<12}{len(cs):>9,}" +
              "".join(f"{pct(cc[k], cs_validos):>12.1f}%" for k in CLASES[:3]) +
              f"{pct(cc['seca'], cs_validos):>8.1f}%")

        if a.inventario:
            print(base_stats + f"{pct(opp, len(cs)):>7.1f}%" + f"{score(cs, a.inventario):>8.1f}")
        else:
            print(base_stats + f"{score(cs, a.inventario):>8.1f}")

    cs_validos_todo = len([c for c in todo if c["tipo"] != "oportunidad_perdida"])
    opp_todo = sum(1 for c in todo if c["tipo"] == "oportunidad_perdida")
    cc = Counter(c["clase"] for c in todo if c["tipo"] != "oportunidad_perdida")

    if a.inventario:
        print("  " + "-" * 83)
        base_stats = (f"  {'TOTAL':<12}{len(todo):>9,}" +
              "".join(f"{pct(cc[k], cs_validos_todo):>12.1f}%" for k in CLASES[:3]) +
              f"{pct(cc['seca'], cs_validos_todo):>8.1f}%")
        print(base_stats + f"{pct(opp_todo, len(todo)):>7.1f}%" + f"{score(todo, a.inventario):>8.1f}")
    else:
        print("  " + "-" * 75)
        base_stats = (f"  {'TOTAL':<12}{len(todo):>9,}" +
              "".join(f"{pct(cc[k], cs_validos_todo):>12.1f}%" for k in CLASES[:3]) +
              f"{pct(cc['seca'], cs_validos_todo):>8.1f}%")
        print(base_stats + f"{score(todo, a.inventario):>8.1f}")

    print(f"\n  Como se resolvio cada negacion (total):")
    for k in CLASES:
        print(f"    {k:<14}{cc[k]:>8,}{pct(cc[k], len(todo)):>8.1f}%")
    adj = sum(1 for c in todo if c["por_adjunto"])
    print(f"\n    de las 'alternativa', {adj:,} se detectaron por FOTO "
          f"({pct(adj, cc['alternativa']):.1f}%) -- regla 5 del Maestro")

    print(f"\n  Por tipo de negacion (el dialecto de cada cartera, regla 10):")
    print(f"\n  {'Tipo':<24}{'Veces':>9}{'% secas':>10}")
    print("  " + "-" * 44)
    for tipo, n in Counter(c["tipo"] for c in todo).most_common():
        sec = sum(1 for c in todo if c["tipo"] == tipo and c["clase"] == "seca")
        print(f"  {tipo:<24}{n:>9,}{pct(sec, n):>9.1f}%")

    print(f"\n  POR VENDEDOR (30+ negaciones)")
    if a.inventario:
        print(f"\n  {'Vendedor':<24}{'Cartera':<11}{'Negac.':>8}{'alternat.':>11}"
              f"{'seguim.':>10}{'SECAS':>9}{'OPP':>8}{'IRN':>8}{'Confianza':>12}")
        print("  " + "-" * 101)
    else:
        print(f"\n  {'Vendedor':<24}{'Cartera':<11}{'Negac.':>8}{'alternat.':>11}"
              f"{'seguim.':>10}{'SECAS':>9}{'IRN':>8}{'Confianza':>12}")
        print("  " + "-" * 93)

    porv = defaultdict(list)
    for c in todo:
        porv[(c["vendedor"], c["cartera"])].append(c)
    filas = [(v, ca, cs) for (v, ca), cs in porv.items() if len(cs) >= 30]
    for v, ca, cs in sorted(filas, key=lambda x: -score(x[2], a.inventario)):
        cs_val = [c for c in cs if c["tipo"] != "oportunidad_perdida"]
        if not cs_val:
            continue
        cc2 = Counter(c["clase"] for c in cs_val)
        opp_v = sum(1 for c in cs if c["tipo"] == "oportunidad_perdida")
        confianza = calcular_nivel_confianza(len(cs_val))

        base_stats = (f"  {esc(v)[:23]:<24}{ca:<11}{len(cs_val):>8,}"
              f"{pct(cc2['alternativa'], len(cs_val)):>10.1f}%"
              f"{pct(cc2['seguimiento'], len(cs_val)):>9.1f}%"
              f"{pct(cc2['seca'], len(cs_val)):>8.1f}%")

        if a.inventario:
            print(base_stats + f"{pct(opp_v, len(cs)):>7.1f}%" + f"{score(cs, a.inventario):>8.1f}{confianza:>12}")
        else:
            print(base_stats + f"{score(cs, a.inventario):>8.1f}{confianza:>12}")

    if a.inventario:
        import alternos as ALTMOD
        prod, por_cabeza = ALTMOD.indice(con)
        ALT.REAL = {}
        for (x,) in con.execute(
                "select codigo from producto where codigo is not null"):
            ALT.REAL.setdefault(SOL.nk(x), x)
        elegibles = [c for c in todo if c["fecha"][:10] >= DESDE_INVENTARIO]
        fechas = sorted({c["fecha"][:10] for c in elegibles})
        stock = existencias_por_fecha(con, fechas)
        print("\n" + "=" * 88)
        print(f"  CRUCE CON INVENTARIO - habia algo que ofrecer?")
        print(f"  solo del {DESDE_INVENTARIO} en adelante: antes no hay carga diaria")
        print("=" * 88)
        ver = Counter()
        ver_seca = Counter()
        detalle = []
        for c in elegibles:
            v, d = resolver_pieza(con, c, stock, prod, por_cabeza)
            ver[v] += 1
            if c["clase"] == "seca":
                ver_seca[v] += 1
            c["veredicto"], c["detalle_inv"] = v, d
            if v in ("NEGO teniendo existencia", "agotado, HABIA alterno",
                     "HABIA algo con existencia") and c["clase"] == "seca":
                detalle.append(c)
        n = len(elegibles)
        print(f"\n  negaciones en la ventana: {n:,}  "
              f"(de {len(todo):,} del mes)")
        print(f"\n  {'Veredicto':<38}{'Todas':>9}{'%':>8}{'Secas':>9}{'%':>8}")
        print("  " + "-" * 72)
        for k, v in ver.most_common():
            ns = ver_seca[k]
            print(f"  {k:<38}{v:>9,}{pct(v, n):>7.1f}%{ns:>9,}"
                  f"{pct(ns, max(1, sum(ver_seca.values()))):>7.1f}%")
        det = n - ver["no determinable"]
        print(f"\n  determinables: {det:,} ({pct(det, n):.1f}%)")
        if det:
            mal = (ver["NEGO teniendo existencia"] +
                   ver["agotado, HABIA alterno"] + ver["HABIA algo con existencia"])
            print(f"  de esas, habia algo que ofrecer: {mal:,} ({pct(mal, det):.1f}%)")
        print(f"\n  Ejemplos de SECAS donde si habia algo:")
        for c in detalle[:12]:
            print(f"    {c['fecha'][:10]} {c['cartera']:<10} "
                  f"{esc(c['vendedor'])[:18]:<19} {c['veredicto']}")
            print(f"       pidio: {esc(c['pedido'])[:62]}")
            print(f"       dijo : {esc(c['negacion'])[:62]}")
            print(f"       habia: {esc(c['detalle_inv'])[:62]}")
        if a.excel:
            import pandas as pd
            dfi = pd.DataFrame([{
                "Fecha": c["fecha"][:16], "Cartera": c["cartera"],
                "Vendedor": c["vendedor"],
                "Cliente": cts_inv.get((c["cartera"], c["contact_id"]),
                                       c["contact_id"]),
                "Resolucion": c["clase"], "Veredicto": c["veredicto"],
                "Habia": c["detalle_inv"], "Que pidio": c["pedido"],
                "Que respondio": c["negacion"],
                "VALIDO (S/N)": "", "OBSERVACION": ""}
                for c in elegibles if c["veredicto"] != "no determinable"])
            ruta = os.path.join(REPORTES, f"Negaciones vs inventario {a.mes}.xlsx")
            try:
                dfi.to_excel(ruta, index=False, sheet_name="Determinables")
            except PermissionError:
                print(f"\n  [!] lo tenes abierto: {ruta}")
            else:
                print(f"\n  -> {ruta}")

    if a.muestra:
        print("\n" + "=" * 88)
        print("  MUESTRA AL AZAR PARA REVISAR A OJO")
        print("=" * 88 + "\n")
        random.seed(11)
        for c in random.sample(todo, min(a.muestra, len(todo))):
            print(f"  [{c['clase']:<11}|{c['tipo']:<20}] {esc(c['negacion'])[:58]}")
            print(f"       pedido:    {esc(c['pedido'])[:66]}")
            print(f"       evidencia: {esc(c['evidencia']) or '(nada: seca)'}")

    if a.excel:
        import pandas as pd
        os.makedirs(REPORTES, exist_ok=True)
        cts = dict(((r[0], r[1]), r[2]) for r in con.execute(
            "select cartera, contact_id, nombre from contacto"))

        data_todas = []
        for c in todo:
            pts_res = calcular_resolucion(c) if c["tipo"] != "oportunidad_perdida" else 0
            pts_proact = calcular_proactividad(c) if c["tipo"] != "oportunidad_perdida" else 0
            pts_conv = calcular_calidad_conversacional(c) if c["tipo"] != "oportunidad_perdida" else 0
            pts_gest = calcular_gestion_oportunidad(c) if c["tipo"] != "oportunidad_perdida" and "veredicto" in c else (20 if c["tipo"] != "oportunidad_perdida" else 0)

            data_todas.append({
                "Cartera": c["cartera"], "Fecha": c["fecha"],
                "Vendedor": c["vendedor"],
                "Cliente": cts.get((c["cartera"], c["contact_id"]), c["contact_id"]),
                "Tipo": c["tipo"], "Resolucion_Principal": c["clase"],
                "Clases_Detectadas": c.get("clases_str", ""),
                "Por foto": "SI" if c["por_adjunto"] else "",
                "Que pidio": c["pedido"], "Que respondio": c["negacion"],
                "Evidencia_Auditoria": c.get("evidencia", "") + "\n\n(Posterior: " + c.get("posterior", "") + ")",
                "Pts_Resolucion": pts_res,
                "Pts_Proactividad": pts_proact,
                "Pts_Conversacional": pts_conv,
                "Pts_Gestion_Oportunidad": pts_gest,
                "VALIDO (S/N)": "", "OBSERVACION": ""
            })

        df = pd.DataFrame(data_todas)

        res_data = []
        for (v, ca), cs in porv.items():
            cs_val = [c for c in cs if c["tipo"] != "oportunidad_perdida"]
            if not cs_val:
                continue

            opp = sum(1 for c in cs if c["tipo"] == "oportunidad_perdida")

            row = {
                "Vendedor": v, "Cartera": ca,
                "Negaciones_Validas": len(cs_val)
            }
            if a.inventario:
                row["Oportunidades_Perdidas_Total"] = opp

            for k in CLASES:
                row[k] = round(pct(sum(1 for c in cs_val if c["clase"] == k), len(cs_val)), 1)

            if a.inventario:
                row["OPP_Pct"] = round(pct(opp, len(cs)), 1)

            row["IRN"] = round(score(cs, a.inventario), 1)
            row["Confianza"] = calcular_nivel_confianza(len(cs_val))
            res_data.append(row)

        res = pd.DataFrame(res_data).sort_values("IRN")
        ruta = os.path.join(REPORTES, f"Negaciones {a.mes}.xlsx")
        try:
            with pd.ExcelWriter(ruta, engine="openpyxl") as w:
                res.to_excel(w, index=False, sheet_name="Por vendedor")
                df[df["Resolucion_Principal"] == "seca"].to_excel(
                    w, index=False, sheet_name="Secas")
                df.to_excel(w, index=False, sheet_name="Todas")
        except PermissionError:
            print(f"\n  [!] lo tenes abierto: {ruta}")
        else:
            print(f"\n  -> {ruta}")
    print()
    con.close()


if __name__ == "__main__":
    main()
