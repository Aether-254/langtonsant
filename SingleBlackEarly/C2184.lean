import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2184 : checkSingleBlackFast (-90, -69) 21173 .east (36, 26) (20, -59) = true := by
  decide +kernel

end LangtonsAnt
