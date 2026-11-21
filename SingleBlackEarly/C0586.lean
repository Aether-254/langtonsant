import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0586 : checkSingleBlackFast (20, 6) 9336 .north (-7, 7) (3, -17) = true := by
  decide +kernel

end LangtonsAnt
