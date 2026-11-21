import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1635 : checkSingleBlackFast (-38, -19) 19776 .north (21, 17) (-47, -9) = true := by
  decide +kernel

end LangtonsAnt
