import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0670 : checkSingleBlackFast (15, -10) 9072 .north (2, -5) (-22, -3) = true := by
  decide +kernel

end LangtonsAnt
