import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0233 : checkSingleBlackFast (5, 9) 4141 .west (-7, 5) (-15, -12) = true := by
  decide +kernel

end LangtonsAnt
