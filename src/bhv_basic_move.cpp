// -*-c++-*-

/*
 *Copyright:

 Copyright (C) Hidehisa AKIYAMA

 This code is free software; you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation; either version 3, or (at your option)
 any later version.

 This code is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with this code; see the file COPYING.  If not, write to
 the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

 *EndCopyright:
 */

/////////////////////////////////////////////////////////////////////

#ifdef HAVE_CONFIG_H
#include <config.h>
#include <bits/stdc++.h>
#endif

#include "bhv_basic_move.h"

#include "strategy.h"

#include "bhv_basic_tackle.h"

#include <rcsc/action/basic_actions.h>
#include <rcsc/action/body_go_to_point.h>
#include <rcsc/action/body_intercept.h>
#include <rcsc/action/neck_turn_to_ball_or_scan.h>
#include <rcsc/action/neck_turn_to_low_conf_teammate.h>

#include <rcsc/player/player_agent.h>
#include <rcsc/player/debug_client.h>
#include <rcsc/player/intercept_table.h>

#include <rcsc/common/logger.h>
#include <rcsc/common/server_param.h>

#include "neck_offensive_intercept_neck.h"
using namespace rcsc;

#include <bits/stdc++.h>
 
#define ll long long
#define sz(x) ((int) (x).size())
#define all(x) (x).begin(), (x).end()
#define vi vector<int>
#define pii pair<int, int>
#define rep(i, a, b) for(int i = (a); i < (b); i++)
using namespace std;
template<typename T>
using minpq = priority_queue<T, vector<T>, greater<T>>;
 
using ftype = long double;
const ftype eps = 1e-12, INF = 1e100;

// struct de ponto
struct pt {
    ftype x, y;
    pt(ftype x = 0, ftype y = 0) : x(x), y(y) {}

    pt operator+(const pt &o) const {
        return pt(x + o.x, y + o.y);
    }
    pt operator-(const pt &o) const {
        return pt(x - o.x, y - o.y);
    }
    pt operator*(const ftype &f) const {
        return pt(x * f, y * f);
    }

    pt rot() const {
        return pt(-y, x);
    }

    ftype dot(const pt &o) const {
        return x * o.x + y * o.y;
    }
    ftype cross(const pt &o) const {
        return x * o.y - y * o.x;
    }

    ftype len() const {
        return hypotl(x, y);
    }

    bool operator<(const pt &o) const {
        return make_pair(x, y) < make_pair(o.x, o.y);
    }
};

// funções auxiliares.
bool collinear(pt a, pt b) {
    return abs(a.cross(b)) < eps;
}

bool diferent(pt a, pt b){
    return (a.x != b.x) && (a.y != b.y);
}

pt lineline(pt a, pt b, pt c, pt d) {
    return a + (b - a) * ((c - a).cross(d - c) / (b - a).cross(d - c));
}

pt circumcenter(pt a, pt b, pt c) {
    b = (a + b) * 0.5;
    c = (a + c) * 0.5;
    return lineline(b, b + (b - a).rot(), c, c + (c - a).rot());
}

// Verificar se o triângulo existe.
bool nonDegenareted(pt a, pt b, pt c){
    double sza = sqrt ( (b.x - a.x)*(b.x - a.x) + (b.y - a.y)*(b.y - a.y));
    double szb = sqrt ( (c.x - b.x)*(c.x - b.x) + (c.y - b.y)*(c.y - b.y));
    double szc = sqrt ( (a.x - c.x)*(a.x - c.x) + (a.y - c.y)*(a.y - c.y));
    return sza + szb > szc && sza + szc > szb && szb + szc > sza;
}

ftype sweepx;
// Arco que vai ser gerado com o algoritmo de fortuna.
struct arc {
    mutable pt p, q;
    mutable int id = 0, i;
    arc(pt p, pt q, int i) : p(p), q(q), i(i) {}

    ftype gety(ftype x) const {
        if(q.y == INF) return INF;
        x += eps;
        pt med = (p + q) * 0.5;
        pt dir = (p - med).rot();
        ftype D = (x - p.x) * (x - q.x);
        return med.y + ((med.x - x) * dir.x + sqrtl(D) * dir.len()) / dir.y;
    }
    bool operator<(const ftype &y) const {
        return gety(sweepx) < y;
    }
    bool operator<(const arc &o) const {
        return gety(sweepx) < o.gety(sweepx);
    }
};

using beach = multiset<arc, less<>>;

// Struct que lida com evento
struct event {
    ftype x;
    int id;
    beach::iterator it;
    event(ftype x, int id, beach::iterator it) : x(x), id(id), it(it) {}
    bool operator<(const event &e) const {
        return x > e.x;
    }
};

struct fortune {
    beach line; 
    vector<pair<pt, int>> v; 
    priority_queue<event> Q;
    vector<pii> edges; 
    vector<bool> valid;
    int n, ti; 
    // Colocar no vetor e ordernar
    fortune(vector<pt> p) {
        n = sz(p);
        v.resize(n);
        rep(i, 0, n) v[i] = {p[i], i};
        sort(all(v));
    }
    // Update após achar um ponto
    void upd(beach::iterator it) {
        if(it->i == -1) return;
        valid[-it->id] = false;
        auto a = prev(it);
        if(collinear(it->q - it->p, a->p - it->p)) return; 
        it->id = --ti;
        valid.push_back(true);
        pt c = circumcenter(it->p, it->q, a->p);
        ftype x = c.x + (c - it->p).len();
        if(x > sweepx - eps && a->gety(x) + eps > it->gety(x)) {
            Q.push(event(x, it->id, it));
        }
    }
    // Nova aresta de Delauney.
    void add_edge(int i, int j) {
        if(i == -1 || j == -1) return;
        edges.push_back({v[i].second, v[j].second});
    }
    void add(int i) {
        pt p = v[i].first;
        auto c = line.lower_bound(p.y);
        auto b = line.insert(c, arc(p, c->p, i));
        auto a = line.insert(b, arc(c->p, p, c->i));
        add_edge(i, c->i);
        upd(a); upd(b); upd(c);
    }
    void remove(beach::iterator it) {
        auto a = prev(it);
        auto b = next(it);
        line.erase(it);
        a->q = b->p;
        add_edge(a->i, b->i);
        upd(a); upd(b);
    }
    void solve(ftype X = 1e9) {
        X *= 3;
        line.insert(arc(pt(-X, -X), pt(-X, X), -1));
        line.insert(arc(pt(-X, X), pt(INF, INF), -1));
        rep(i, 0, n) {
            Q.push(event(v[i].first.x, i, line.end()));
        }
        ti = 0;
        valid.assign(1, false);
        while(!Q.empty()) {
            event e = Q.top(); Q.pop();
            sweepx = e.x;
            if(e.id >= 0) {
                add(e.id);
            }else if(valid[-e.id]) {
                remove(e.it);
            }
        }
    }
};

bool
Bhv_BasicMove::execute( PlayerAgent * agent )
{
    dlog.addText( Logger::TEAM,
                  __FILE__": Bhv_BasicMove" );

    //-----------------------------------------------
    // tackle
    if ( Bhv_BasicTackle( 0.8, 80.0 ).execute( agent ) ){
        return true;
    }

    const WorldModel & wm = agent->world();
    const int self_min = wm.interceptTable()->selfReachCycle();
    const int mate_min = wm.interceptTable()->teammateReachCycle();
    const int opp_min = wm.interceptTable()->opponentReachCycle();

    /*Inicialmente vamos gerar a triangulação de Delauney e depois converter para o diagrama de voronoi.*/

    // Pegando todas as posições dos jogadores adversários para gerar o diagrama de voronoi.
    vector<pt> opponents;
    for( PlayerPtrCont::const_iterator it = wm.opponentsFromSelf().begin(); it != wm.opponentsFromSelf().end(); it++ ){
        pt opponent;
        opponent.x = (*it)->pos().x;
        opponent.y = (*it)->pos().y;
        opponents.push_back(opponent);
    } 
    // Utilizando o algoritmo de Fortune para gerar a triangulação.

    struct fortune fort(opponents);
    fort.solve();
    int sz = opponents.size();

    // Declarando variáveis e vetores que serão utilizados no resto no código.

    vector<int> delauney_vertices[sz];
    vector<pt> voronoi_vertices;
    vector<double> weight;

    Vector2D player_pos = wm.self().pos();
    Vector2D ball_pos = wm.ball().pos();
    Vector2D target_point = Strategy::i().getPosition( wm.self().unum() ); 

    const PlayerObject * mate_nxt_to_ball = wm.getTeammateNearestToBall(10);
    const PlayerObject * opp_nxt_to_ball = wm.getOpponentNearestToBall(10);

    int number = wm.self().unum();
    int offside_line = wm.offsideLineX();
    int inside_voronoi_radius = 0;
    double dist = 1e9;
    double dist_from_ball = wm.self().distFromBall();
    double voronoi_radius = 10;
    double dist_from_nxt_mate, dist_from_nxt_opp;

    // Cada fort.edge[i] é uma aresta da triangulação de Delauney. Sendo assim vamos montar o grafo  
    for(int i = 0;i < fort.edges.size();i++){
        delauney_vertices[fort.edges[i].first].push_back(fort.edges[i].second);
    }

    // Um dos pontos de referência para fazer um jogador ir para o vértice de voronoi é a distância em relação a bola
    // Por isso, existe a variáveis voronoi_radius para indicar o raio no qual os jogadores irão para o vértice de voronoi.
    // Além disso, a variável inside_voronoi_radius é usada para evitar que muitos jogadores fiquem aglomerados muito próximos um do outro.

    for( PlayerPtrCont::const_iterator it = wm.teammatesFromSelf().begin(); it != wm.teammatesFromSelf().end(); it++ ){
        pt teammate;
        teammate.x = (*it)->pos().x;
        teammate.y = (*it)->pos().y;

        double dx = (teammate.x - ball_pos.x);
        double dy = (teammate.y - ball_pos.y);
        double dist_mate_to_ball = sqrt(dx * dx + dy * dy);

        if(dist_mate_to_ball < voronoi_radius) {
            inside_voronoi_radius++;
        }

    }

    // Para gerar o diagrama de voronoi a partir da triangulação de Delauney vamos buscar todos os triangulos formados pelo grafo de Delauney.
    // A partir disso, para cada triângulo, vamos calcular o circumcentro do triangulo, que será um vértice de Voronoi.
    // Pois o diagrama de voronoi é o grafo dual do grafo planar de Delauney.

    for(int i = 0;i < sz;i++){
        for(auto j : delauney_vertices[i]){
            for(auto k : delauney_vertices[j]){
                if(i != j && j != k && i != k && nonDegenareted(opponents[i], opponents[j], opponents[k])){
                    pt v_vertice = circumcenter(opponents[i], opponents[j], opponents[k]);
                    double dx = (v_vertice.x - ball_pos.x);
                    double dy = (v_vertice.y - ball_pos.y);
                    double voronoi_vertice_to_ball = sqrt(dx*dx + dy*dy);
                    if(v_vertice.x <= offside_line && voronoi_vertice_to_ball < voronoi_radius && inside_voronoi_radius < 4){
                        voronoi_vertices.push_back(circumcenter(opponents[i], opponents[j], opponents[k]));
                    }
                } 

            }
        }
    }

    int v_v_size = voronoi_vertices.size();
    weight.resize(v_v_size, 1e9);

    // Para decidir para qual vértice de voronoi vamos ir, em todos os vértice e calcular o "peso"
    // O peso é definido como sendo o vértice mais próximo da bola e mais distante dos jogadores adversários.

    for(int i = 0;i < v_v_size;i++){

        // Calculando a distância para a bola e a distância da bola para o vértice de voronoi.

        double dx = (mate_nxt_to_ball->pos().x - voronoi_vertices[i].x) ;
        double dy = (mate_nxt_to_ball->pos().y - voronoi_vertices[i].y) ;
        dist_from_nxt_mate = sqrt(dx*dx+dy*dy);
        dx = (opp_nxt_to_ball->pos().x - voronoi_vertices[i].x);
        dy = (opp_nxt_to_ball->pos().y - voronoi_vertices[i].y);
        dist_from_nxt_opp = sqrt(dx*dx+dy*dy);
    
        if(number >= 9 && number <= 11) {
            // Jogadores do ataque na grande área ou perto dela.
            if(wm.ourOffenseLineX() > 25  && player_pos.x >= wm.ourOffenseLineX() - 3 && player_pos.x <= wm.ourOffenseLineX() + 8) {
                if((number == 11 && ball_pos.y > player_pos.y) || (number == 11 && ball_pos.y < player_pos.y)) {
                    weight[i] = abs(ball_pos.y - player_pos.y);
                } else {
                    weight[i] = dist_from_nxt_mate - dist_from_nxt_opp;
                } 
            } 
            // no campo de ataque
            else if( wm.ourOffenseLineX() > 0 && player_pos.x >= wm.ourOffenseLineX() - 7 && player_pos.x <= wm.ourOffenseLineX() + 7) {
                // Se estivermos perto da bola, vamos considerar apenas a diferença no eixo y.
                if( abs(ball_pos.y - player_pos.y) <= 5) {
                    weight[i] = abs(ball_pos.y - player_pos.y);
                // Com a distância maior , calculamos a diferenaça.
                } else if(abs(ball_pos.y - player_pos.y) <= 20) {
                    weight[i] = dist_from_nxt_mate - dist_from_nxt_opp;
                } 

            } 
            //Estando os jogadores de ataque na defesa, vamos utilizar os vértices de voronoi se existe parceiro com a bola.
            else if(wm.ourDefenseLineX() > 0 && wm.lastKickerSide() == wm.ourSide()) {
                weight[i] = dist_from_nxt_mate - dist_from_nxt_opp;
            }
        } else if (number >= 6 && number <= 8) {
            // Se estiver no meio do campo e a posição estiver no intervalo considerando o vértice de voronoi.
            if(wm.ourOffenseLineX() <= 20 && wm.ourDefenseLineX() <= 10 && player_pos.x <= voronoi_vertices[i].x - 8 && player_pos.x >= voronoi_vertices[i].x + 8) {
                weight[i] = dist_from_nxt_mate - dist_from_nxt_opp;
            }else if(wm.ourOffenseLineX() > 20) {
                // Se os jogadores do meio campo estão no ataque
                // Se tiver perto considero apenas o eixo y.
                if( abs(ball_pos.y - player_pos.y) <= 5) {
                    weight[i] = abs(ball_pos.y - player_pos.y);
                // se estiver um pouco mais longe considero a distância.
                } else if(abs(ball_pos.y - player_pos.y) <= 20) {
                    weight[i] = dist_from_nxt_mate - dist_from_nxt_opp;
                } 
            }
            // Se os meio campistas estiverem na defesa e o seu time estiver com a posse de bola, ir para o vértice de voronoi.
            else if(wm.ourDefenseLineX() > 10  && wm.lastKickerSide() == wm.ourSide() ){
                weight[i] = dist_from_nxt_mate - dist_from_nxt_opp;
            }
        } else if(number >= 2 && number <= 5) {
            // Os vértices de voronoi podem ser uma posição vulnerável no ataque, então 
            if( wm.ourDefenseLineX() > 0 
            && opp_nxt_to_ball->pos().x >= voronoi_vertices[i].x - 2 && opp_nxt_to_ball->pos().x <= voronoi_vertices[i].x + 2
            && opp_nxt_to_ball->pos().y >= voronoi_vertices[i].y - 2 && opp_nxt_to_ball->pos().y <= voronoi_vertices[i].y + 2) {
                weight[i] = dist_from_nxt_mate - dist_from_nxt_opp;
            }
        }
    }

    // Evitar que dois agentes estejam no mesmo local ao mesmo tempo.
    // Vamos iterar por todos os jogadores e verificar se algum outro jogador já está no vértice de voronoi.
    // Se não tiver, vamos fazer o agente se mover para lá.

    for(int i = 0;i < v_v_size;i++){

        if(weight[i] < dist) {    
            bool goToVoronoiVertice = true;
            for(PlayerPtrCont::const_iterator it = wm.teammatesFromSelf().begin(); it != wm.teammatesFromSelf().end(); it++){
                pt teammate;
                teammate.x = (*it)->pos().x;
                teammate.y = (*it)->pos().y;

                if(teammate.x >= voronoi_vertices[i].x - 3 && teammate.x <= voronoi_vertices[i].x + 3
                && teammate.y >= voronoi_vertices[i].y - 3 && teammate.y <= voronoi_vertices[i].y + 3) {
                    goToVoronoiVertice = false;
                }
            }

            if(goToVoronoiVertice) { 
                target_point.x = voronoi_vertices[i].x;
                target_point.y = voronoi_vertices[i].y;
                dist = weight[i];
            }
        }

    }

    // --------------------------------------------------------
    // chase ball
    if ( ! wm.existKickableTeammate()
         && ( self_min <= 3
              || ( self_min <= mate_min
                   && self_min < opp_min + 3 )
              )
         )
    {
        dlog.addText( Logger::TEAM,
                      __FILE__": intercept" );
        Body_Intercept().execute( agent );
        agent->setNeckAction( new Neck_OffensiveInterceptNeck() );

        return true;
    }

    const double dash_power = Strategy::get_normal_dash_power( wm );

    double dist_thr = wm.ball().distFromSelf() * 0.1; //Limite de distancia.
    if ( dist_thr < 1.0 ) dist_thr = 1.0; //tem que ser pelo menos 1.

    dlog.addText( Logger::TEAM,
                  __FILE__": Bhv_BasicMove target=(%.1f %.1f) dist_thr=%.2f",
                  target_point.x, target_point.y,
                  dist_thr );

    agent->debugClient().addMessage( "BasicMove%.0f", dash_power ); 
    agent->debugClient().setTarget( target_point );
    agent->debugClient().addCircle( target_point, dist_thr ); 


    if ( ! Body_GoToPoint( target_point, dist_thr, dash_power
                           ).execute( agent ) )
    {
        Body_TurnToBall().execute( agent );
    }

    // Virar para a bola.
    if ( wm.existKickableOpponent()
         && wm.ball().distFromSelf() < 18.0 )
    {
        agent->setNeckAction( new Neck_TurnToBall() );
    }
    // FALTA ENTENDER
    else
    {
        agent->setNeckAction( new Neck_TurnToBallOrScan() );
    }

    return true;
}