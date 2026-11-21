import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0315 : checkSingleBlackFast (2, 11) 9517 .west (-5, 5) (-21, -14) = true := by
  decide +kernel

end LangtonsAnt
