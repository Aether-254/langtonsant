import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0487 : checkSingleBlackFast (5, 14) 25556 .north (-7, 10) (-9, -26) = true := by
  decide +kernel

end LangtonsAnt
