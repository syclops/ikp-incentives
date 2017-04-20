/** IKP Payout Analysis
 *  Author: Steve Matsumoto
 */

/**
 * Define a fractional type (a real between 0 and 1), used to calculate
 * termination payouts.
 */
newtype frac = r:real | 0 as real <= r <= 1 as real

/**
 * Define allowable actions in our game as well as the game itself. There are
 * three types of actions:
 *   * CARegisterAction: whether the CA issuing a certificate for the domain
 *     registers with the IKP authority or not.
 *   * CAIssueAction: whether the CA issues an authorized certificate for the
 *     domain (i.e., a certificate conforming to the domain's DCP) or not.
 *   * DetectorAction: whether the detector reports the certificate as
 *     unauthorized or not.
 * A one-shot game is simply a set of these three actions.
 */
datatype CARegisterAction = Register | NoRegister
datatype CAIssueAction = IssueGoodCert | IssueBadCert
datatype DetectorAction = Report | NoReport
datatype OneShotGame = Decisions(reg:CARegisterAction, iss:CAIssueAction,
                                 det:DetectorAction)

/**
 * Define an RP by its price, affected-domain payout, termination payout, and
 * detection payout.
 */
datatype RP = RP(price:nat, affDomPayout:nat, termPayout:nat, detPayout:nat)

function splitDomain(rp:RP, remLife:frac, minTermPayout:nat) : int
{
  ((remLife as real) * (((rp.termPayout as int)
                         - (minTermPayout as int)) as real)).Floor
    + (minTermPayout as int)
}

lemma splitBounds()
  ensures forall rp:RP, remLife:frac, minTermPayout:nat
            :: TermPayoutConstraint(minTermPayout, rp)
               ==> (minTermPayout as int)
                   <= splitDomain(rp, remLife, minTermPayout)
                   <= (rp.termPayout as int);
{
  // Nothing to do here.
}

function DomainPayout(g:OneShotGame, rp:RP, remLife:frac,
                      minTermPayout:nat): int
{
  if (g.det == NoReport || g.iss == IssueGoodCert) then
    -(rp.price as int)
  else if (g.reg == Register) then
    (rp.affDomPayout as int) + splitDomain(rp, remLife, minTermPayout)
      - (rp.price as int)
  else
    splitDomain(rp, remLife, minTermPayout) - (rp.price as int)
}

function DetectorPayout(g:OneShotGame, rp:RP, reportingFee:nat) : int
{
  if (g.det == NoReport) then
    0
  else if (g.iss == IssueGoodCert) then
    -(reportingFee as int)
  else if (g.reg == Register) then
    (rp.detPayout as int) - (reportingFee as int)
  else
    0
}

function CAPayout(g:OneShotGame, rp:RP, remLife:frac, minTermPayout:nat) : int
{
  if (g.reg == NoRegister || g.det == NoReport || g.iss == IssueGoodCert) then
    0
  else
    (rp.price as int) - splitDomain(rp, remLife, minTermPayout)
      - (rp.affDomPayout as int) - (rp.detPayout as int)
}

predicate ReportingConstraint(reportingFee:nat, rp:RP)
{
  0 < reportingFee < rp.detPayout
}

predicate TermPayoutConstraint(minTermPayout:nat, rp:RP)
{
  0 < minTermPayout <= rp.termPayout
}

predicate RPPriceConstraint(minTermPayout:nat, rp:RP)
{
  rp.termPayout < rp.price < rp.affDomPayout + minTermPayout
}

predicate CADomCollusionResistance(g1:OneShotGame, g2:OneShotGame, rp:RP,
                                   remLife:frac, minTermPayout:nat)
{
  CAPayout(g1, rp, remLife, minTermPayout) + DomainPayout(g1, rp, remLife,
                                                          minTermPayout)
    <= CAPayout(g2, rp, remLife, minTermPayout) + DomainPayout(g2, rp, remLife,
                                                               minTermPayout)
}

/*lemma CADeployment()*/
/*{*/
/*}*/

/*lemma CAIncentives()*/
/*{*/
/*}*/

/**
 * Prove the incentivization of reporting a bad certificate.
 */
lemma ReportingIncentive()
  ensures forall g1:OneShotGame, g2:OneShotGame, rp:RP, rf:nat
            :: ReportingConstraint(rf, rp)
               && g1.reg.Register? && g2.reg.Register?
               && g1.iss.IssueBadCert? && g2.iss.IssueBadCert?
               && g1.det.Report? && g2.det.NoReport?
            ==> DetectorPayout(g1, rp, rf) > DetectorPayout(g2, rp, rf);
{
  // Nothing to do here.
}


/**
 * Prove punishment of a domain that spuriously reports a certificate as
 * unauthorized.
 */
lemma NoSpuriousReports()
  ensures forall g1:OneShotGame, g2:OneShotGame, rp:RP, rf:nat
            :: ReportingConstraint(rf, rp)
               && g1.iss.IssueGoodCert? && g2.iss.IssueGoodCert?
               && g1.det.Report? && g2.det.NoReport?
              ==> DetectorPayout(g1, rp, rf) < DetectorPayout(g2, rp, rf);
{
  // Nothing to do here.
}

/**
 * Prove the absence of collusion attacks.
 *
 * Prove that no malicious external CA can collude with either a domain, a
 * detector, or both to generate a profit.
 *
 * Postconditions:
 *   For all one-shot RP games where the CA has not registered and has issued a
 *   bad certificate,
 */
lemma NoCollusionProfits()
  ensures forall g:OneShotGame, rp:RP, remLife:frac, minTermPayout:nat,
                 reportingFee:nat
                 | g.reg.NoRegister? && TermPayoutConstraint(minTermPayout, rp)
                   && RPPriceConstraint(minTermPayout, rp)
                 :: (CAPayout(g, rp, remLife, minTermPayout)
                     + DomainPayout(g, rp, remLife, minTermPayout) <= 0)
                    && (CAPayout(g, rp, remLife, minTermPayout)
                        + DetectorPayout(g, rp, reportingFee) <= 0)
                    && (CAPayout(g, rp, remLife, minTermPayout)
                        + DomainPayout(g, rp, remLife, minTermPayout)
                        + DetectorPayout(g, rp, reportingFee) <= 0);
{
  splitBounds();
}

/*
lemma DomainIncentive()
  ensures forall g1:OneShotGame, g2:OneShotGame, rp:RP, remLife:frac,
                 minTermPayout:nat
                   :: TermPayoutConstraint(minTermPayout, rp)
                      && RPPriceConstraint(minTermPayout, rp)
                      && g1.iss.IssueBadCert? && g1.det.Report?
                      && g2.iss.IssueBadCert? && g2.det.NoReport?
                      ==> DomainPayout(g1, rp, remLife, minTermPayout)
                          >= DomainPayout(g2, rp, remLife, minTermPayout);
{
  // Nothing to do here.
}
*/

/*
lemma CAIncentive()
  ensures forall g1:OneShotGame, g2:OneShotGame, rp:RP, remLife:frac,
                 minTermPayout:nat
                   :: TermPayoutConstraint(minTermPayout, rp)
                      && RPPriceConstraint(minTermPayout, rp)
                      && g1.iss.IssueGoodCert? && g2.iss.IssueBadCert?
                      ==> CAPayout(g1, rp, remLife, minTermPayout)
                          >= CAPayout(g2, rp, remLife, minTermPayout);
{
  // Nothing to do here.
}
*/

