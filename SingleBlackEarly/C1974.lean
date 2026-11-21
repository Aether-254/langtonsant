import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1974 : checkSingleBlackFast (-73, -46) 19458 .north (28, 21) (-55, -34) = true := by
  decide +kernel

end LangtonsAnt
