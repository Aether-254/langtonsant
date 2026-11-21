import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2201 : checkSingleBlackFast (-92, -70) 20587 .east (36, 30) (3, -48) = true := by
  decide +kernel

end LangtonsAnt
