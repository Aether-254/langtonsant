import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0517 : checkSingleBlackFast (-7, -5) 12628 .north (-5, 5) (-1, -25) = true := by
  decide +kernel

end LangtonsAnt
