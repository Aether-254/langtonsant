import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1944 : checkSingleBlackFast (-66, -48) 28875 .east (36, 24) (-5, -46) = true := by
  decide +kernel

end LangtonsAnt
